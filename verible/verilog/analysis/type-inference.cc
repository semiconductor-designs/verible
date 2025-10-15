// Copyright 2025 The Verible Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "verible/verilog/analysis/type-inference.h"

#include <memory>
#include <string>

#include "verible/common/text/concrete-syntax-tree.h"
#include "verible/common/text/symbol.h"
#include "verible/common/text/tree-utils.h"
#include "verible/common/util/casts.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/parser/verilog-token-enum.h"

namespace verilog {
namespace analysis {

TypeInference::TypeInference(const SymbolTable* symbol_table)
    : symbol_table_(symbol_table) {}

const Type* TypeInference::InferType(const verible::Symbol& expr) {
  stats_.total_inferences++;

  // Check cache first
  const Type* cached = CheckCache(expr_cache_, &expr);
  if (cached) return cached;

  // Infer based on expression type
  if (expr.Kind() == verible::SymbolKind::kLeaf) {
    // It's a token (literal or identifier)
    const auto* leaf = &verible::SymbolCastToLeaf(expr);
    auto type = std::make_unique<Type>(InferLiteral(leaf->get()));
    return StoreInCache(expr_cache_, &expr, std::move(type));
  }

  // It's a node - check the node type
  const auto* node = &verible::SymbolCastToNode(expr);
  if (!node) {
    return nullptr;
  }

  const auto tag = static_cast<NodeEnum>(node->Tag().tag);

  std::unique_ptr<Type> inferred_type;

  switch (tag) {
    case NodeEnum::kUnqualifiedId:
    case NodeEnum::kLocalRoot:
      return InferIdentifier(expr);

    case NodeEnum::kBinaryExpression:
      // Binary operation: lhs op rhs
      // Simplified: assume standard binary expression structure
      return nullptr;  // TODO: Implement with proper CST traversal
      break;

    case NodeEnum::kUnaryPrefixExpression:
      // Unary operation: op expr
      // Simplified: assume standard unary expression structure
      return nullptr;  // TODO: Implement with proper CST traversal
      break;

    case NodeEnum::kConcatenationExpression:
      return InferConcat(expr);

    case NodeEnum::kFunctionCall:
      return InferFunctionCall(expr);

    default:
      // Unknown expression type - return unknown
      inferred_type = std::make_unique<Type>();
      inferred_type->base_type = PrimitiveType::kUnknown;
  }

  if (inferred_type) {
    return StoreInCache(expr_cache_, &expr, std::move(inferred_type));
  }

  return nullptr;
}

const Type* TypeInference::GetDeclaredType(const SymbolTableNode& symbol) {
  // Check cache first
  const Type* cached = CheckCache(decl_cache_, &symbol);
  if (cached) return cached;

  const SymbolInfo& info = symbol.Value();
  auto type = std::make_unique<Type>(ExtractDeclaredType(info.declared_type));

  return StoreInCache(decl_cache_, &symbol, std::move(type));
}

const Type* TypeInference::InferBinaryOp(const verible::Symbol& lhs,
                                         const verible::Symbol& rhs,
                                         const verible::TokenInfo& op) {
  const Type* lhs_type = InferType(lhs);
  const Type* rhs_type = InferType(rhs);

  if (!lhs_type || !rhs_type) {
    auto unknown = std::make_unique<Type>();
    unknown->base_type = PrimitiveType::kUnknown;
    return unknown.release();
  }

  auto result = std::make_unique<Type>();

  switch (op.token_enum()) {
    case '+':
    case '-':
    case '*':
    case '/':
    case '%':
      // Arithmetic operators
      if (lhs_type->IsReal() || rhs_type->IsReal()) {
        result->base_type = PrimitiveType::kReal;
      } else {
        result->base_type = PrimitiveType::kLogic;
        int lhs_width = lhs_type->GetWidth();
        int rhs_width = rhs_type->GetWidth();
        result->dimensions = {std::max(lhs_width, rhs_width)};
        result->is_signed = lhs_type->is_signed && rhs_type->is_signed;
      }
      break;

    case '&':
    case '|':
    case '^':
      // Bitwise operators - result width is max of operands
      result->base_type = PrimitiveType::kLogic;
      result->dimensions = {std::max(lhs_type->GetWidth(), rhs_type->GetWidth())};
      break;

    case TK_LAND:
    case TK_LOR:
      // Logical operators - result is 1-bit
      result->base_type = PrimitiveType::kLogic;
      result->dimensions = {1};
      break;

    case TK_EQ:
    case TK_NE:
    case '<':
    case '>':
    case TK_LE:
    case TK_GE:
      // Comparison operators - result is 1-bit
      result->base_type = PrimitiveType::kLogic;
      result->dimensions = {1};
      break;

    case TK_LS:
    case TK_RS:
      // Shift operators - result width is left operand width
      result->base_type = PrimitiveType::kLogic;
      result->dimensions = {lhs_type->GetWidth()};
      result->is_signed = lhs_type->is_signed;
      break;

    default:
      result->base_type = PrimitiveType::kUnknown;
  }

  return result.release();
}

const Type* TypeInference::InferUnaryOp(const verible::Symbol& expr,
                                        const verible::TokenInfo& op) {
  const Type* operand_type = InferType(expr);
  if (!operand_type) {
    auto unknown = std::make_unique<Type>();
    unknown->base_type = PrimitiveType::kUnknown;
    return unknown.release();
  }

  auto result = std::make_unique<Type>();

  switch (op.token_enum()) {
    case '+':
    case '-':
    case '~':
      // Unary arithmetic/bitwise - preserve operand type
      *result = *operand_type;
      break;

    case '!':
      // Logical negation - result is 1-bit
      result->base_type = PrimitiveType::kLogic;
      result->dimensions = {1};
      break;

    case '&':
    case '|':
    case '^':
      // Reduction operators - result is 1-bit
      result->base_type = PrimitiveType::kLogic;
      result->dimensions = {1};
      break;

    default:
      result->base_type = PrimitiveType::kUnknown;
  }

  return result.release();
}

void TypeInference::ClearCache() {
  expr_cache_.clear();
  decl_cache_.clear();
  stats_ = Stats();
}

Type TypeInference::InferLiteral(const verible::TokenInfo& token) {
  Type type;

  // Simplified literal inference
  // Full implementation would parse the token text and determine exact type
  switch (token.token_enum()) {
    case TK_DecNumber:
      // Integer literal - default to 32-bit logic
      type.base_type = PrimitiveType::kLogic;
      type.dimensions = {32};
      break;

    case TK_RealTime:
      type.base_type = PrimitiveType::kReal;
      break;

    case TK_StringLiteral:
      type.base_type = PrimitiveType::kString;
      break;

    default:
      // For all other tokens (identifiers, other literals)
      // Default to single-bit logic
      type.base_type = PrimitiveType::kLogic;
      type.dimensions = {1};
  }

  return type;
}

const Type* TypeInference::InferIdentifier(const verible::Symbol& id) {
  // Extract identifier name
  std::string id_name(verible::StringSpanOfSymbol(id));

  // Simplified: return 32-bit logic for identifiers
  // Full implementation would look up symbol in symbol table
  // and return its declared type
  auto result = std::make_unique<Type>();
  result->base_type = PrimitiveType::kLogic;
  result->dimensions = {32};
  return StoreInCache(expr_cache_, &id, std::move(result));
}

const Type* TypeInference::InferConcat(const verible::Symbol& concat) {
  // Concatenation {a, b, c} - sum of all widths
  // Simplified: return 32-bit logic for concatenations
  // Full implementation would traverse children and sum widths
  auto result = std::make_unique<Type>();
  result->base_type = PrimitiveType::kLogic;
  result->dimensions = {32};
  return StoreInCache(expr_cache_, &concat, std::move(result));
}

const Type* TypeInference::InferReplication(const verible::Symbol& replication) {
  // Replication {N{a}} - width is N * width(a)
  // Simplified: return 32-bit logic for replications
  // Full implementation would evaluate count and multiply by expression width
  auto result = std::make_unique<Type>();
  result->base_type = PrimitiveType::kLogic;
  result->dimensions = {32};
  return StoreInCache(expr_cache_, &replication, std::move(result));
}

const Type* TypeInference::InferSelect(const verible::Symbol& select) {
  // Bit/part select: a[3:0] or a[5]
  // Simplified: return single-bit logic for selects
  // Full implementation would analyze the select range
  auto result = std::make_unique<Type>();
  result->base_type = PrimitiveType::kLogic;
  result->dimensions = {1};
  return StoreInCache(expr_cache_, &select, std::move(result));
}

const Type* TypeInference::InferFunctionCall(const verible::Symbol& call) {
  // Function call - look up function return type
  // Simplified: return 32-bit logic for function calls
  // Full implementation would look up function return type in symbol table
  auto result = std::make_unique<Type>();
  result->base_type = PrimitiveType::kLogic;
  result->dimensions = {32};
  return StoreInCache(expr_cache_, &call, std::move(result));
}

const Type* TypeInference::InferConditional(const verible::Symbol& conditional) {
  // Ternary operator: cond ? true_expr : false_expr
  // Result type is the common type of true_expr and false_expr
  // Simplified: return 32-bit logic for conditional expressions
  // Full implementation would infer types of both branches and return wider type
  auto result = std::make_unique<Type>();
  result->base_type = PrimitiveType::kLogic;
  result->dimensions = {32};
  return StoreInCache(expr_cache_, &conditional, std::move(result));
}

Type TypeInference::ExtractDeclaredType(const DeclarationTypeInfo& type_info) {
  Type type;

  // For now, return a basic logic type
  // Full implementation would parse type_info.syntax_origin
  type.base_type = PrimitiveType::kLogic;
  type.dimensions = {1};

  // TODO: Parse actual type from syntax_origin
  // This would involve CST traversal to extract:
  // - Base type (logic, int, real, etc.)
  // - Dimensions ([7:0], [3:0][7:0], etc.)
  // - Signedness
  // - User-defined types

  return type;
}

}  // namespace analysis
}  // namespace verilog

