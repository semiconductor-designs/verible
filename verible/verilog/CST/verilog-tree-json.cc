// Copyright 2017-2020 The Verible Authors.
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

#include "verible/verilog/CST/verilog-tree-json.h"

#include <ostream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>

#include "nlohmann/json.hpp"
#include "verible/common/text/concrete-syntax-leaf.h"
#include "verible/common/text/concrete-syntax-tree.h"
#include "verible/common/text/symbol.h"
#include "verible/common/text/token-info-json.h"
#include "verible/common/text/token-info.h"
#include "verible/common/text/tree-utils.h"
#include "verible/common/text/visitors.h"
#include "verible/common/util/casts.h"
#include "verible/common/util/value-saver.h"
#include "verible/verilog/CST/expression.h"  // for UnwrapExpression, ExtractIdentifierFromExpression
#include "verible/verilog/CST/functions.h"  // for GetFunctionCallName
#include "verible/verilog/CST/verilog-nonterminals.h"  // for NodeEnumToString
#include "verible/verilog/parser/verilog-token-classifications.h"
#include "verible/verilog/parser/verilog-token-enum.h"
#include "verible/verilog/parser/verilog-token.h"

using nlohmann::json;

namespace verilog {

// Helper function: Map operator symbol to operation name
static std::string MapOperatorToOperation(std::string_view operator_text) {
  static const std::unordered_map<std::string_view, std::string> op_map = {
      // Arithmetic
      {"+", "add"},
      {"-", "subtract"},
      {"*", "multiply"},
      {"/", "divide"},
      {"%", "modulo"},
      {"**", "power"},

      // Comparison
      {"==", "eq"},
      {"!=", "ne"},
      {"<", "lt"},
      {"<=", "le"},
      {">", "gt"},
      {">=", "ge"},
      {"===", "case_eq"},
      {"!==", "case_ne"},

      // Logical
      {"&&", "logical_and"},
      {"||", "logical_or"},

      // Bitwise
      {"&", "bit_and"},
      {"|", "bit_or"},
      {"^", "bit_xor"},
      {"~^", "bit_xnor"},
      {"^~", "bit_xnor"},

      // Shift
      {"<<", "shift_left"},
      {">>", "shift_right"},
      {"<<<", "shift_left_arith"},
      {">>>", "shift_right_arith"},

      // Unary (will be used in Phase 2)
      {"~", "bit_not"},
      {"!", "logical_not"},

      // Ternary (will be used in Phase 2)
      {"?", "ternary"},
  };

  auto it = op_map.find(operator_text);
  return it != op_map.end() ? it->second : std::string(operator_text);
}

// Helper function: Classify operand type (reference, literal, or expression)
static std::string ClassifyOperandType(const verible::Symbol &operand) {
  // Unwrap kExpression wrapper if present (use existing utility)
  const verible::Symbol *unwrapped = UnwrapExpression(operand);
  if (!unwrapped) return "expression";

  // Descend through singleton nodes (nodes with only one child)
  unwrapped = verible::DescendThroughSingletons(*unwrapped);
  if (!unwrapped) return "expression";

  // Check if it's a literal (number, string, etc.) - check leaves first
  if (unwrapped->Kind() == verible::SymbolKind::kLeaf) {
    const auto &leaf =
        verible::down_cast<const verible::SyntaxTreeLeaf &>(*unwrapped);
    auto token_type = verilog_tokentype(leaf.Tag().tag);

    // Check for numeric literals
    if (token_type == TK_DecNumber || token_type == TK_RealTime ||
        token_type == TK_TimeLiteral || token_type == TK_StringLiteral) {
      return "literal";
    }

    // Check for based numbers (e.g., 8'hFF, 2'b01)
    if (token_type == TK_BinDigits || token_type == TK_DecDigits ||
        token_type == TK_HexDigits || token_type == TK_OctDigits ||
        token_type == TK_UnBasedNumber) {
      return "literal";
    }
    
    // If it's an identifier leaf, it's a reference
    if (IsIdentifierLike(token_type)) {
      return "reference";
    }
  }

  // Check if it's a node
  if (unwrapped->Kind() == verible::SymbolKind::kNode) {
    const auto &node =
        verible::down_cast<const verible::SyntaxTreeNode &>(*unwrapped);
    NodeEnum tag = NodeEnum(node.Tag().tag);
    
    // kNumber nodes represent numeric literals (sized or unsized)
    if (tag == NodeEnum::kNumber) {
      return "literal";
    }
    
    // References and unqualified IDs are references
    if (tag == NodeEnum::kReference || tag == NodeEnum::kUnqualifiedId) {
      return "reference";
    }
    
    // If it's another expression node, it's a nested expression
    if (tag == NodeEnum::kBinaryExpression ||
        tag == NodeEnum::kUnaryPrefixExpression ||
        tag == NodeEnum::kConditionExpression ||
        tag == NodeEnum::kFunctionCall) {
      return "expression";
    }
  }

  // Default: assume it's an expression
  return "expression";
}

// Helper function: Map unary operator to operation name
static std::string MapUnaryOperatorToOperation(std::string_view operator_text) {
  static const std::unordered_map<std::string_view, std::string> unary_op_map = {
      // Logical
      {"!", "logical_not"},
      
      // Bitwise
      {"~", "bitwise_not"},
      
      // Arithmetic
      {"-", "negate"},
      {"+", "unary_plus"},
      
      // Reduction operators
      {"&", "reduction_and"},
      {"|", "reduction_or"},
      {"^", "reduction_xor"},
      {"~&", "reduction_nand"},
      {"~|", "reduction_nor"},
      {"^~", "reduction_xnor"},
      {"~^", "reduction_xnor"},
  };

  auto it = unary_op_map.find(operator_text);
  return it != unary_op_map.end() ? it->second : std::string(operator_text);
}

// Helper method: Add metadata for unary expressions (operator operand)
static void AddUnaryExpressionMetadata(json &node_json,
                                        const verible::SyntaxTreeNode &node) {
  json metadata = json::object();

  // Unary expression structure: [operator, operand]
  // Index 0 = operator, Index 1 = operand
  if (node.size() < 2) return;  // Invalid structure

  // Extract operator from node[0]
  const auto *op_symbol = node[0].get();
  if (!op_symbol || op_symbol->Kind() != verible::SymbolKind::kLeaf) return;

  const auto &op_leaf = verible::SymbolCastToLeaf(*op_symbol);
  std::string_view operator_text = op_leaf.get().text();

  metadata["operation"] = MapUnaryOperatorToOperation(operator_text);
  metadata["operator"] = std::string(operator_text);

  // Extract operand
  json operands = json::array();
  
  if (node[1]) {
    json operand = json::object();
    operand["role"] = "operand";
    operand["type"] = ClassifyOperandType(*node[1]);
    
    std::string identifier = ExtractIdentifierFromExpression(*node[1]);
    if (!identifier.empty()) {
      operand["identifier"] = identifier;
    }
    
    operands.push_back(operand);
  }

  metadata["operands"] = operands;
  node_json["metadata"] = metadata;
}

// Helper method: Add metadata for function calls
static void AddFunctionCallMetadata(json &node_json,
                                     const verible::SyntaxTreeNode &node) {
  json metadata = json::object();
  metadata["operation"] = "function_call";
  
  NodeEnum node_tag = NodeEnum(node.Tag().tag);
  std::string func_name;
  json operands = json::array();
  
  // Handle kSystemTFCall (system functions like $clog2, $display, etc.)
  if (node_tag == NodeEnum::kSystemTFCall) {
    // kSystemTFCall structure: [SystemTFIdentifier, kParenGroup]
    if (node.size() >= 1 && node[0]) {
      // node[0] is the SystemTFIdentifier leaf
      if (node[0]->Kind() == verible::SymbolKind::kLeaf) {
        const auto &id_leaf = verible::down_cast<const verible::SyntaxTreeLeaf &>(*node[0]);
        func_name = std::string(id_leaf.get().text());
      }
    }
    
    // Extract arguments from kParenGroup (node[1])
    if (node.size() >= 2 && node[1]) {
      const verible::Symbol *paren_group = node[1].get();
      if (paren_group && paren_group->Kind() == verible::SymbolKind::kNode) {
        const auto &pg_node = verible::down_cast<const verible::SyntaxTreeNode &>(*paren_group);
        
        // kParenGroup: ["(", argument_list, ")"]
        if (pg_node.size() >= 3 && pg_node[1]) {
          const verible::Symbol *arg_list = pg_node[1].get();
          if (arg_list && arg_list->Kind() == verible::SymbolKind::kNode) {
            const auto &arg_list_node = verible::down_cast<const verible::SyntaxTreeNode &>(*arg_list);
            
            // Arguments at even indices: 0, 2, 4, ...
            for (size_t i = 0; i < arg_list_node.size(); i += 2) {
              if (arg_list_node[i]) {
                json argument = json::object();
                argument["role"] = "argument";
                argument["type"] = ClassifyOperandType(*arg_list_node[i]);
                
                std::string identifier = ExtractIdentifierFromExpression(*arg_list_node[i]);
                if (!identifier.empty()) {
                  argument["identifier"] = identifier;
                }
                
                operands.push_back(argument);
              }
            }
          }
        }
      }
    }
  } else {
    // Handle kFunctionCall (regular function calls)
    // kFunctionCall structure: [kReferenceCallBase or kReference]
    //  - kReferenceCallBase: [reference, paren_group] (for function calls with args)
    //  - kReference: [reference_id] (for simple references, no args)
    
    const verible::Symbol *ref_base = nullptr;
    if (node.size() >= 1 && node[0]) {
      ref_base = node[0].get();
    }
    
    if (ref_base && ref_base->Kind() == verible::SymbolKind::kNode) {
      const auto &ref_node = verible::down_cast<const verible::SyntaxTreeNode &>(*ref_base);
      NodeEnum ref_tag = NodeEnum(ref_node.Tag().tag);
      
      if (ref_tag == NodeEnum::kReferenceCallBase && ref_node.size() >= 2) {
        // Has arguments: kReferenceCallBase[0]=reference, [1]=paren_group
        if (ref_node[0]) {
          std::string_view func_text = verible::StringSpanOfSymbol(*ref_node[0]);
          func_name = std::string(func_text);
        }
        
        // Extract arguments from paren_group
        if (ref_node[1]) {
          const verible::Symbol *paren_group = ref_node[1].get();
          if (paren_group && paren_group->Kind() == verible::SymbolKind::kNode) {
            const auto &pg_node = verible::down_cast<const verible::SyntaxTreeNode &>(*paren_group);
            
            // paren_group: ["(", arg_list, ")"]
            if (pg_node.size() >= 3 && pg_node[1]) {
              const verible::Symbol *arg_list = pg_node[1].get();
              if (arg_list && arg_list->Kind() == verible::SymbolKind::kNode) {
                const auto &arg_list_node = verible::down_cast<const verible::SyntaxTreeNode &>(*arg_list);
                
                // Arguments at even indices: 0, 2, 4, ...
                for (size_t i = 0; i < arg_list_node.size(); i += 2) {
                  if (arg_list_node[i]) {
                    json argument = json::object();
                    argument["role"] = "argument";
                    argument["type"] = ClassifyOperandType(*arg_list_node[i]);
                    
                    std::string identifier = ExtractIdentifierFromExpression(*arg_list_node[i]);
                    if (!identifier.empty()) {
                      argument["identifier"] = identifier;
                    }
                    
                    operands.push_back(argument);
                  }
                }
              }
            }
          }
        }
      } else if (ref_tag == NodeEnum::kReference) {
        // Simple reference, no arguments
        if (ref_node.size() >= 1 && ref_node[0]) {
          std::string_view func_text = verible::StringSpanOfSymbol(*ref_node[0]);
          func_name = std::string(func_text);
        }
      }
    }
  }
  
  metadata["function_name"] = func_name;
  metadata["operands"] = operands;
  node_json["metadata"] = metadata;
}

// Helper method: Add metadata for ternary expressions (condition ? true : false)
static void AddTernaryExpressionMetadata(json &node_json,
                                          const verible::SyntaxTreeNode &node) {
  json metadata = json::object();
  metadata["operation"] = "conditional";
  metadata["operator"] = "?:";

  json operands = json::array();

  // Ternary expression structure: [condition, "?", true_expr, ":", false_expr]
  // Indices: 0=condition, 2=true_value, 4=false_value
  if (node.size() >= 5) {
    // Condition operand (index 0)
    if (node[0]) {
      json condition_operand = json::object();
      condition_operand["role"] = "condition";
      condition_operand["type"] = ClassifyOperandType(*node[0]);
      std::string condition_id = ExtractIdentifierFromExpression(*node[0]);
      if (!condition_id.empty()) {
        condition_operand["identifier"] = condition_id;
      }
      operands.push_back(condition_operand);
    }

    // True value operand (index 2)
    if (node[2]) {
      json true_operand = json::object();
      true_operand["role"] = "true_value";
      true_operand["type"] = ClassifyOperandType(*node[2]);
      std::string true_id = ExtractIdentifierFromExpression(*node[2]);
      if (!true_id.empty()) {
        true_operand["identifier"] = true_id;
      }
      operands.push_back(true_operand);
    }

    // False value operand (index 4)
    if (node[4]) {
      json false_operand = json::object();
      false_operand["role"] = "false_value";
      false_operand["type"] = ClassifyOperandType(*node[4]);
      std::string false_id = ExtractIdentifierFromExpression(*node[4]);
      if (!false_id.empty()) {
        false_operand["identifier"] = false_id;
      }
      operands.push_back(false_operand);
    }
  }

  metadata["operands"] = operands;
  node_json["metadata"] = metadata;
}

class VerilogTreeToJsonConverter : public verible::SymbolVisitor {
 public:
  explicit VerilogTreeToJsonConverter(std::string_view base);

  void Visit(const verible::SyntaxTreeLeaf &) final;
  void Visit(const verible::SyntaxTreeNode &) final;

  json TakeJsonValue() { return std::move(json_); }

 private:
  // Add metadata for binary expressions
  void AddBinaryExpressionMetadata(const verible::SyntaxTreeNode &node,
                                   json &value);

 protected:
  // Range of text spanned by syntax tree, used for offset calculation.
  const verible::TokenInfo::Context context_;

  // JSON tree root
  json json_;

  // Pointer to JSON value of currently visited symbol in its parent's
  // children list.
  json *value_;
};

VerilogTreeToJsonConverter::VerilogTreeToJsonConverter(std::string_view base)
    : context_(base,
               [](std::ostream &stream, int e) {
                 stream << TokenTypeToString(static_cast<verilog_tokentype>(e));
               }),
      value_(&json_) {}

void VerilogTreeToJsonConverter::Visit(const verible::SyntaxTreeLeaf &leaf) {
  const verilog_tokentype tokentype =
      static_cast<verilog_tokentype>(leaf.Tag().tag);
  std::string_view type_str = TokenTypeToString(tokentype);
  // Don't include token's text for operators, keywords, or anything that is a
  // part of Verilog syntax. For such types, TokenTypeToString() is equal to
  // token's text. Exception has to be made for identifiers, because things like
  // "PP_Identifier" or "SymbolIdentifier" (which are values returned by
  // TokenTypeToString()) could be used as Verilog identifier.
  const bool include_text =
      verilog::IsIdentifierLike(tokentype) || (leaf.get().text() != type_str);
  *value_ = verible::ToJson(leaf.get(), context_, include_text);
}

void VerilogTreeToJsonConverter::Visit(const verible::SyntaxTreeNode &node) {
  *value_ = json::object();
  (*value_)["tag"] = NodeEnumToString(static_cast<NodeEnum>(node.Tag().tag));
  
  // Extract and include the full source text for this node
  std::string_view node_text = verible::StringSpanOfSymbol(node);
  if (!node_text.empty()) {
    (*value_)["text"] = std::string(node_text);
  }
  
  // Add metadata for supported expression types
  NodeEnum tag = static_cast<NodeEnum>(node.Tag().tag);
  if (tag == NodeEnum::kBinaryExpression) {
    AddBinaryExpressionMetadata(node, *value_);
  } else if (tag == NodeEnum::kConditionExpression) {
    AddTernaryExpressionMetadata(*value_, node);
  } else if (tag == NodeEnum::kUnaryPrefixExpression) {
    AddUnaryExpressionMetadata(*value_, node);
  } else if (tag == NodeEnum::kFunctionCall) {
    AddFunctionCallMetadata(*value_, node);
  } else if (tag == NodeEnum::kSystemTFCall) {
    AddFunctionCallMetadata(*value_, node);  // System functions use same format
  }
  
  json &children = (*value_)["children"] = json::array();

  {
    const verible::ValueSaver<json *> value_saver(&value_, nullptr);
    for (const auto &child : node.children()) {
      value_ = &children.emplace_back(nullptr);
      // nullptrs from children list are intentionally preserved in JSON as
      // `null` values.
      if (child) child->Accept(this);
    }
  }
}

void VerilogTreeToJsonConverter::AddBinaryExpressionMetadata(
    const verible::SyntaxTreeNode &node, json &value) {
  // Binary expression structure:
  // node[0] = left operand
  // node[1] = operator
  // node[2] = right operand
  // For associative operators (a+b+c), Verible may flatten them:
  // node[0]=a, node[1]=+, node[2]=b, node[3]=+, node[4]=c

  if (node.size() < 3) return;  // Invalid structure

  json metadata = json::object();

  // Extract operator from node[1]
  const auto *op_symbol = node[1].get();
  if (!op_symbol || op_symbol->Kind() != verible::SymbolKind::kLeaf) return;

  const auto &op_leaf = verible::SymbolCastToLeaf(*op_symbol);
  std::string_view operator_text = op_leaf.get().text();

  metadata["operation"] = MapOperatorToOperation(operator_text);
  metadata["operator"] = std::string(operator_text);

  // Extract operands
  json operands = json::array();

  // Process left operand (node[0])
  if (node[0]) {
    json left_operand = json::object();
    left_operand["role"] = "left";
    left_operand["type"] = ClassifyOperandType(*node[0]);

    std::string identifier = ExtractIdentifierFromExpression(*node[0]);
    if (!identifier.empty()) {
      left_operand["identifier"] = identifier;
    } else {
      left_operand["identifier"] = nullptr;
      // Provide full text for nested expressions
      std::string_view operand_text = verible::StringSpanOfSymbol(*node[0]);
      if (!operand_text.empty()) {
        left_operand["expression_text"] = std::string(operand_text);
      }
    }
    operands.push_back(left_operand);
  }

  // Process right operand(s) - node[2], node[4], node[6], etc. for associative
  for (size_t i = 2; i < node.size(); i += 2) {
    if (node[i]) {
      json right_operand = json::object();
      // First right operand gets "right" role, additional ones get "operand"
      right_operand["role"] = (i == 2) ? "right" : "operand";
      right_operand["type"] = ClassifyOperandType(*node[i]);

      std::string identifier = ExtractIdentifierFromExpression(*node[i]);
      if (!identifier.empty()) {
        right_operand["identifier"] = identifier;
      } else {
        right_operand["identifier"] = nullptr;
        // Provide full text for nested expressions
        std::string_view operand_text = verible::StringSpanOfSymbol(*node[i]);
        if (!operand_text.empty()) {
          right_operand["expression_text"] = std::string(operand_text);
        }
      }
      operands.push_back(right_operand);
    }
  }

  metadata["operands"] = operands;
  value["metadata"] = metadata;
}

json ConvertVerilogTreeToJson(const verible::Symbol &root,
                              std::string_view base) {
  VerilogTreeToJsonConverter converter(base);
  root.Accept(&converter);
  return converter.TakeJsonValue();
}

}  // namespace verilog
