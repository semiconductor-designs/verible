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

#include <functional>
#include <ostream>
#include <regex>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

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
#include "verible/verilog/CST/declaration.h"  // for declaration utilities
#include "verible/verilog/CST/expression.h"  // for UnwrapExpression, ExtractIdentifierFromExpression
#include "verible/verilog/CST/functions.h"  // for GetFunctionCallName
#include "verible/verilog/CST/identifier.h"  // for AutoUnwrapIdentifier
#include "verible/verilog/CST/statement.h"  // for GetProceduralTimingControlFromAlways, etc.
#include "verible/verilog/CST/type.h"  // for type utilities
#include "verible/verilog/CST/verilog-matchers.h"  // for NodekTypeDeclaration
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

// Helper function: Check if a signal name is likely a reset signal
static bool IsLikelyResetSignal(std::string_view signal_name) {
  // Common reset signal name patterns
  std::string lower_name;
  lower_name.reserve(signal_name.size());
  for (char c : signal_name) {
    lower_name += std::tolower(c);
  }
  
  // Check for reset-like patterns
  return (lower_name.find("rst") != std::string::npos ||
          lower_name.find("reset") != std::string::npos ||
          lower_name.find("clear") != std::string::npos ||
          lower_name.find("clr") != std::string::npos ||
          lower_name.find("init") != std::string::npos);
}

// Helper function: Check if a signal name is likely an enable signal
static bool IsLikelyEnableSignal(std::string_view signal_name) {
  // Common enable signal name patterns
  std::string lower_name;
  lower_name.reserve(signal_name.size());
  for (char c : signal_name) {
    lower_name += std::tolower(c);
  }
  
  // Check for enable-like patterns
  return (lower_name.find("en") != std::string::npos ||
          lower_name.find("enable") != std::string::npos ||
          lower_name.find("valid") != std::string::npos ||
          lower_name.find("ready") != std::string::npos ||
          lower_name.find("strobe") != std::string::npos ||
          lower_name.find("stb") != std::string::npos ||
          lower_name.find("req") != std::string::npos);
}

// Helper function: Add location metadata (line and column numbers)
static json AddLocationMetadata(const verible::Symbol &symbol, 
                                  std::string_view base) {
  json location = json::object();
  
  // Get text span for this symbol
  auto text_span = verible::StringSpanOfSymbol(symbol);
  if (text_span.empty() || base.empty()) {
    return location;  // No location info available
  }
  
  // Calculate byte offsets
  size_t start_offset = text_span.begin() - base.begin();
  size_t end_offset = text_span.end() - base.begin();
  
  // Calculate line and column numbers
  int start_line = 1, start_col = 1;
  int end_line = 1, end_col = 1;
  
  for (size_t i = 0; i < start_offset && i < base.size(); ++i) {
    if (base[i] == '\n') {
      start_line++;
      start_col = 1;
    } else {
      start_col++;
    }
  }
  
  end_line = start_line;
  end_col = start_col;
  for (size_t i = start_offset; i < end_offset && i < base.size(); ++i) {
    if (base[i] == '\n') {
      end_line++;
      end_col = 1;
    } else {
      end_col++;
    }
  }
  
  location["start_line"] = start_line;
  location["start_column"] = start_col;
  location["end_line"] = end_line;
  location["end_column"] = end_col;
  
  return location;
}

// ============================================================================
// Phase A: Type Resolution Metadata
// ============================================================================

// Typedef information extracted from CST
struct TypedefInfo {
  std::string typedef_name;
  std::string base_type;  // e.g., "logic", "bit"
  int width;
  bool is_signed;
  bool is_packed;
  bool is_enum;
  int enum_member_count;
  bool is_struct;
  int struct_field_count;
  std::vector<std::string> struct_field_names;
  bool is_union;
  int union_member_count;
  bool is_parameterized;
  bool is_array;
  int array_dimensions;
  std::vector<int> dimension_sizes;
  int resolution_depth;
  int definition_line;
  int definition_column;
  std::string dimension_string;
  std::string resolved_type_string;
};

// Symbol information for cross-reference tracking (Phase B)
struct SymbolInfo {
  std::string symbol_name;
  std::string symbol_type;  // "variable", "port", "parameter", "module", etc.
  int definition_line;
  int definition_column;
  std::vector<int> usage_lines;  // Lines where symbol is used
  std::vector<int> usage_columns;
  std::vector<int> redeclaration_lines;  // Lines with duplicate declarations
  std::vector<int> redeclaration_columns;
  bool is_port;
  std::string port_direction;  // "input", "output", "inout"
  bool is_parameter;
  bool has_definition;
  bool has_redeclaration;
};

// Scope information for hierarchy tracking (Phase C - lightweight)
struct ScopeInfo {
  std::string scope_name;
  std::string scope_type;  // "module", "function", "task", "block"
  std::string parent_scope;
  int definition_line;
};

// Dataflow information for signal tracking (Phase D - lightweight)
struct DataflowInfo {
  std::string signal_name;
  bool has_driver;
  std::string driver_type;  // "continuous", "blocking", "nonblocking"
  bool is_used;
  int driver_line;
};

// Helper: Calculate line number from symbol position in source text
// Uses same logic as AddLocationMetadata for consistency
static int CalculateLineNumber(const verible::Symbol& symbol, std::string_view base) {
  auto text_span = verible::StringSpanOfSymbol(symbol);
  if (text_span.empty() || base.empty()) {
    return 1;
  }
  
  // Calculate start offset (same as AddLocationMetadata)
  size_t start_offset = text_span.begin() - base.begin();
  
  // Calculate line number
  int line = 1;
  for (size_t i = 0; i < start_offset && i < base.size(); ++i) {
    if (base[i] == '\n') {
      line++;
    }
  }
  
  return line;
}

// Helper: Calculate column number from symbol position
// Uses same logic as AddLocationMetadata for consistency
static int CalculateColumnNumber(const verible::Symbol& symbol, std::string_view base) {
  auto text_span = verible::StringSpanOfSymbol(symbol);
  if (text_span.empty() || base.empty()) {
    return 1;
  }
  
  // Calculate start offset (same as AddLocationMetadata)
  size_t start_offset = text_span.begin() - base.begin();
  
  // Calculate column number
  int column = 1;
  for (size_t i = 0; i < start_offset && i < base.size(); ++i) {
    if (base[i] == '\n') {
      column = 1;  // Reset column after newline
    } else {
      column++;
    }
  }
  
  return column;
}

// Helper: Build a symbol table from the syntax tree (Phase B)
static std::unordered_map<std::string, SymbolInfo> BuildSymbolTable(
    const verible::Symbol& root, std::string_view source_text) {
  std::unordered_map<std::string, SymbolInfo> symbol_table;
  
  // Track variable declarations (kDataDeclaration -> kRegisterVariable)
  auto var_decls = verible::SearchSyntaxTree(root, NodekDataDeclaration());
  for (const auto& match : var_decls) {
    const auto* decl_node = match.match;
    if (!decl_node || decl_node->Kind() != verible::SymbolKind::kNode) continue;
    
    // Search for kRegisterVariable nodes within the declaration
    auto reg_var_matches = verible::SearchSyntaxTree(*decl_node, NodekRegisterVariable());
    for (const auto& reg_match : reg_var_matches) {
      const auto* reg_node = reg_match.match;
      if (!reg_node || reg_node->Kind() != verible::SymbolKind::kNode) continue;
      
      const auto& reg_var_node = verible::SymbolCastToNode(*reg_node);
      
      // The variable name is typically the first leaf (SymbolIdentifier)
      if (reg_var_node.size() > 0 && reg_var_node[0]) {
        const auto* name_symbol = reg_var_node[0].get();
        if (name_symbol && name_symbol->Kind() == verible::SymbolKind::kLeaf) {
          const auto& name_leaf = verible::SymbolCastToLeaf(*name_symbol);
          std::string_view symbol_name_view = name_leaf.get().text();
            std::string symbol_name(symbol_name_view);
            
            // Check if already in table (redeclaration)
            auto existing = symbol_table.find(symbol_name);
            if (existing != symbol_table.end()) {
              // Track redeclaration
              int redecl_line = CalculateLineNumber(*name_symbol, source_text);
              int redecl_column = CalculateColumnNumber(*name_symbol, source_text);
              existing->second.redeclaration_lines.push_back(redecl_line);
              existing->second.redeclaration_columns.push_back(redecl_column);
              existing->second.has_redeclaration = true;
              continue;
            }
            
            SymbolInfo info;
            info.symbol_name = symbol_name;
            info.symbol_type = "variable";
            info.definition_line = CalculateLineNumber(*name_symbol, source_text);
            info.definition_column = CalculateColumnNumber(*name_symbol, source_text);
            info.is_port = false;
            info.is_parameter = false;
            info.has_definition = true;
            info.has_redeclaration = false;
            
            symbol_table[symbol_name] = info;
        }
      }
    }
  }
  
  // Track port declarations (kPortDeclaration)
  auto port_decls = verible::SearchSyntaxTree(root, NodekPortDeclaration());
  for (const auto& match : port_decls) {
    const auto* port_node = match.match;
    if (!port_node || port_node->Kind() != verible::SymbolKind::kNode) continue;
    
    const auto& node = verible::SymbolCastToNode(*port_node);
    
    // Extract port direction from child 0 (input/output/inout)
    std::string port_direction = "unknown";
    if (node.size() > 0 && node[0]) {
      const auto* dir_symbol = node[0].get();
      if (dir_symbol && dir_symbol->Kind() == verible::SymbolKind::kLeaf) {
        const auto& dir_leaf = verible::SymbolCastToLeaf(*dir_symbol);
        port_direction = std::string(dir_leaf.get().text());
      }
    }
    
    // Extract port name from child 3 (kUnqualifiedId)
    if (node.size() > 3 && node[3]) {
      const auto* id_node = node[3].get();
      if (id_node && id_node->Kind() == verible::SymbolKind::kNode) {
        const auto& unqual_id_node = verible::SymbolCastToNode(*id_node);
        if (unqual_id_node.MatchesTag(NodeEnum::kUnqualifiedId) && unqual_id_node.size() > 0 && unqual_id_node[0]) {
          const auto* name_symbol = unqual_id_node[0].get();
          if (name_symbol && name_symbol->Kind() == verible::SymbolKind::kLeaf) {
            const auto& name_leaf = verible::SymbolCastToLeaf(*name_symbol);
            std::string symbol_name(name_leaf.get().text());
            
            // Skip if already in table
            if (symbol_table.find(symbol_name) != symbol_table.end()) continue;
            
            SymbolInfo info;
            info.symbol_name = symbol_name;
            info.symbol_type = "port";
            info.definition_line = CalculateLineNumber(*name_symbol, source_text);
            info.definition_column = CalculateColumnNumber(*name_symbol, source_text);
            info.is_port = true;
            info.port_direction = port_direction;
            info.is_parameter = false;
            info.has_definition = true;
            
            symbol_table[symbol_name] = info;
          }
        }
      }
    }
  }
  
  // Track parameter declarations (kParamDeclaration -> kParamType -> Leaf)
  auto param_decls = verible::SearchSyntaxTree(root, NodekParamDeclaration());
  for (const auto& match : param_decls) {
    const auto* param_node = match.match;
    if (!param_node || param_node->Kind() != verible::SymbolKind::kNode) continue;
    
    const auto& node = verible::SymbolCastToNode(*param_node);
    
    // Get kParamType (child 1)
    if (node.size() > 1 && node[1]) {
      const auto* param_type = node[1].get();
      if (param_type && param_type->Kind() == verible::SymbolKind::kNode) {
        const auto& param_type_node = verible::SymbolCastToNode(*param_type);
        // Parameter name is at child 2, could be direct Leaf or kUnqualifiedId
        if (param_type_node.size() > 2 && param_type_node[2]) {
          const auto* name_node = param_type_node[2].get();
          const verible::Symbol* name_symbol = nullptr;
          
          if (name_node->Kind() == verible::SymbolKind::kLeaf) {
            // Direct Leaf (e.g., parameter int WIDTH = 8)
            name_symbol = name_node;
          } else if (name_node->Kind() == verible::SymbolKind::kNode) {
            // kUnqualifiedId (e.g., parameter WIDTH = 8)
            const auto& unqual_node = verible::SymbolCastToNode(*name_node);
            if (unqual_node.MatchesTag(NodeEnum::kUnqualifiedId) && unqual_node.size() > 0 && unqual_node[0]) {
              name_symbol = unqual_node[0].get();
            }
          }
          
          if (name_symbol && name_symbol->Kind() == verible::SymbolKind::kLeaf) {
            const auto& name_leaf = verible::SymbolCastToLeaf(*name_symbol);
            std::string symbol_name(name_leaf.get().text());
            
            // Skip if already in table
            if (symbol_table.find(symbol_name) != symbol_table.end()) continue;
            
            SymbolInfo info;
            info.symbol_name = symbol_name;
            info.symbol_type = "parameter";
            info.definition_line = CalculateLineNumber(*name_symbol, source_text);
            info.definition_column = CalculateColumnNumber(*name_symbol, source_text);
            info.is_port = false;
            info.is_parameter = true;
            info.has_definition = true;
            
            symbol_table[symbol_name] = info;
          }
        }
      }
    }
  }
  
  // Track all kReference nodes as usages
  auto references = verible::SearchSyntaxTree(root, NodekReference());
  for (const auto& match : references) {
    const auto* ref_node = match.match;
    if (!ref_node) continue;
    
    std::string_view ref_text = verible::StringSpanOfSymbol(*ref_node);
    std::string symbol_name(ref_text);
    
    // Extract just the identifier (remove array indices, field access, etc.)
    size_t bracket_pos = symbol_name.find('[');
    if (bracket_pos != std::string::npos) {
      symbol_name = symbol_name.substr(0, bracket_pos);
    }
    size_t dot_pos = symbol_name.find('.');
    if (dot_pos != std::string::npos) {
      symbol_name = symbol_name.substr(0, dot_pos);
    }
    
    // Add usage location if symbol exists in table
    auto it = symbol_table.find(symbol_name);
    if (it != symbol_table.end()) {
      int usage_line = CalculateLineNumber(*ref_node, source_text);
      int usage_column = CalculateColumnNumber(*ref_node, source_text);
      
      // Don't add if this is the definition itself
      if (usage_line != it->second.definition_line || 
          usage_column != it->second.definition_column) {
        it->second.usage_lines.push_back(usage_line);
        it->second.usage_columns.push_back(usage_column);
      }
    }
  }
  
  return symbol_table;
}

// Helper: Build a typedef table from the syntax tree (Phase A - basic version)
static std::unordered_map<std::string, TypedefInfo> BuildTypedefTable(
    const verible::Symbol& root, std::string_view source_text) {
  std::unordered_map<std::string, TypedefInfo> typedef_table;
  
  // Find all typedef declarations
  auto typedef_matches = verible::SearchSyntaxTree(root, NodekTypeDeclaration());
  
  for (const auto& match : typedef_matches) {
    const auto* typedef_node = match.match;
    if (!typedef_node || typedef_node->Kind() != verible::SymbolKind::kNode) continue;
    
    const auto& node = verible::SymbolCastToNode(*typedef_node);
    
    // Get typedef name (child 2)
    const verible::Symbol* name_symbol = GetSubtreeAsSymbol(node, NodeEnum::kTypeDeclaration, 2);
    if (!name_symbol || name_symbol->Kind() != verible::SymbolKind::kLeaf) continue;
    const auto& name_leaf = verible::SymbolCastToLeaf(*name_symbol);
    std::string typedef_name(name_leaf.get().text());
    
    // Get referenced type (child 1 - kDataType)
    const verible::Symbol* ref_type = GetSubtreeAsSymbol(node, NodeEnum::kTypeDeclaration, 1);
    if (!ref_type) continue;
    
    // Initialize TypedefInfo
    TypedefInfo info;
    info.typedef_name = typedef_name;
    info.is_signed = false;
    info.is_packed = false;
    info.is_enum = false;
    info.enum_member_count = 0;
    info.is_struct = false;
    info.struct_field_count = 0;
    info.is_union = false;
    info.union_member_count = 0;
    info.is_parameterized = false;
    info.is_array = false;
    info.array_dimensions = 0;
    info.resolution_depth = 1;
    info.definition_line = -1;
    info.definition_column = -1;
    info.dimension_string = "";
    info.width = 0;
    
    // Extract source location from typedef declaration
    std::string_view node_text = verible::StringSpanOfSymbol(node);
    if (!source_text.empty() && node_text.data() >= source_text.data() && 
        node_text.data() < source_text.data() + source_text.size()) {
      size_t offset = node_text.data() - source_text.data();
      int line = 1, column = 1;
      for (size_t i = 0; i < offset && i < source_text.size(); ++i) {
        if (source_text[i] == '\n') {
          line++;
          column = 1;
        } else {
          column++;
        }
      }
      info.definition_line = line;
      info.definition_column = column;
    }
    
    // Get base type with enum/struct/union support
    const verible::Symbol* base_type_symbol = GetBaseTypeFromDataType(*ref_type);
    if (base_type_symbol) {
      if (base_type_symbol->Kind() == verible::SymbolKind::kLeaf) {
        const auto& base_leaf = verible::SymbolCastToLeaf(*base_type_symbol);
        info.base_type = std::string(base_leaf.get().text());
      } else if (base_type_symbol->Kind() == verible::SymbolKind::kNode) {
        const auto& base_node = verible::SymbolCastToNode(*base_type_symbol);
        
        if (base_node.MatchesTag(NodeEnum::kDataTypePrimitive)) {
          // Extract packed dimensions - search through all children of ref_type (kDataType)
          if (ref_type->Kind() == verible::SymbolKind::kNode) {
            const auto& data_type_node = verible::SymbolCastToNode(*ref_type);
            for (const auto& child : data_type_node.children()) {
              if (child && child->Kind() == verible::SymbolKind::kNode) {
                const auto& child_node = verible::SymbolCastToNode(*child);
                if (child_node.MatchesTag(NodeEnum::kPackedDimensions)) {
                  // Extract dimension string
                  info.dimension_string = std::string(verible::StringSpanOfSymbol(child_node));
                  // Calculate width from first dimension [msb:lsb]
                  std::string dim_text = info.dimension_string;
                  size_t colon = dim_text.find(':');
                  if (colon != std::string::npos) {
                    try {
                      int msb = std::stoi(dim_text.substr(1, colon - 1));
                      int lsb = std::stoi(dim_text.substr(colon + 1, dim_text.find(']') - colon - 1));
                      info.width = std::abs(msb - lsb) + 1;
                      info.is_packed = true;
                    } catch (...) {
                      info.is_parameterized = true;
                      info.width = -1;  // Unknown width for parameterized types
                    }
                  }
                  break;  // Found dimensions, stop searching
                }
              }
            }
          }
          
          // Check for signed/unsigned keywords in kDataTypePrimitive children
          for (const auto& child : base_node.children()) {
            if (child && child->Kind() == verible::SymbolKind::kLeaf) {
              const auto& leaf = verible::SymbolCastToLeaf(*child);
              std::string_view text = leaf.get().text();
              if (text == "signed") {
                info.is_signed = true;
              } else if (text == "unsigned") {
                info.is_signed = false;
              }
            }
          }
          
          const verible::Symbol* prim_child = GetSubtreeAsSymbol(base_node, NodeEnum::kDataTypePrimitive, 0);
          if (prim_child && prim_child->Kind() == verible::SymbolKind::kLeaf) {
            const auto& prim_leaf = verible::SymbolCastToLeaf(*prim_child);
            info.base_type = std::string(prim_leaf.get().text());
          } else if (prim_child && prim_child->Kind() == verible::SymbolKind::kNode) {
            const auto& prim_child_node = verible::SymbolCastToNode(*prim_child);
            
            // Check for enum type
            if (prim_child_node.MatchesTag(NodeEnum::kEnumType)) {
              info.is_enum = true;
              
              // Extract enum base type from child 1 (kDataType)
              const verible::Symbol* enum_data_type = GetSubtreeAsSymbol(prim_child_node, NodeEnum::kEnumType, 1);
              if (enum_data_type && enum_data_type->Kind() == verible::SymbolKind::kNode) {
                const auto& enum_dt_node = verible::SymbolCastToNode(*enum_data_type);
                if (enum_dt_node.MatchesTag(NodeEnum::kDataType)) {
                  // Directly extract primitive type from kDataType -> kDataTypePrimitive -> Leaf
                  for (const auto& child : enum_dt_node.children()) {
                    if (child && child->Kind() == verible::SymbolKind::kNode) {
                      const auto& child_node = verible::SymbolCastToNode(*child);
                      
                      // Extract base type from kDataTypePrimitive
                      if (child_node.MatchesTag(NodeEnum::kDataTypePrimitive)) {
                        const verible::Symbol* prim_leaf = GetSubtreeAsSymbol(child_node, NodeEnum::kDataTypePrimitive, 0);
                        if (prim_leaf && prim_leaf->Kind() == verible::SymbolKind::kLeaf) {
                          const auto& leaf = verible::SymbolCastToLeaf(*prim_leaf);
                          info.base_type = std::string(leaf.get().text());
                        }
                      }
                      
                      // Extract dimensions from kPackedDimensions
                      if (child_node.MatchesTag(NodeEnum::kPackedDimensions)) {
                        info.dimension_string = std::string(verible::StringSpanOfSymbol(child_node));
                        // Calculate width
                        std::string dim_text = info.dimension_string;
                        size_t colon = dim_text.find(':');
                        if (colon != std::string::npos) {
                          try {
                            int msb = std::stoi(dim_text.substr(1, colon - 1));
                            int lsb = std::stoi(dim_text.substr(colon + 1, dim_text.find(']') - colon - 1));
                            info.width = std::abs(msb - lsb) + 1;
                            info.is_packed = true;
                          } catch (...) {
                            info.is_parameterized = true;
                            info.width = -1;  // Unknown width for parameterized types
                          }
                        }
                      }
                    }
                  }
                }
              }
              
              // Count enum members from child 2 (kBraceGroup)
              const verible::Symbol* brace_group = GetSubtreeAsSymbol(prim_child_node, NodeEnum::kEnumType, 2);
              if (brace_group && brace_group->Kind() == verible::SymbolKind::kNode) {
                const auto& brace_node = verible::SymbolCastToNode(*brace_group);
                if (brace_node.MatchesTag(NodeEnum::kBraceGroup) && brace_node.size() > 1) {
                  const verible::Symbol* enum_list = brace_node[1].get();
                  if (enum_list && enum_list->Kind() == verible::SymbolKind::kNode) {
                    const auto& enum_list_node = verible::SymbolCastToNode(*enum_list);
                    if (enum_list_node.MatchesTag(NodeEnum::kEnumNameList)) {
                      for (const auto& child : enum_list_node.children()) {
                        if (child && child->Kind() == verible::SymbolKind::kNode) {
                          const auto& child_node = verible::SymbolCastToNode(*child);
                          if (child_node.MatchesTag(NodeEnum::kEnumName)) {
                            info.enum_member_count++;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            // Check for struct type
            else if (prim_child_node.MatchesTag(NodeEnum::kStructType)) {
              info.is_struct = true;
              info.base_type = "struct";
              
              // Check for packed keyword at child 1
              const verible::Symbol* signing = GetSubtreeAsSymbol(prim_child_node, NodeEnum::kStructType, 1);
              if (signing && signing->Kind() == verible::SymbolKind::kNode) {
                const auto& signing_node = verible::SymbolCastToNode(*signing);
                if (signing_node.MatchesTag(NodeEnum::kPackedSigning)) {
                  std::string_view signing_text = verible::StringSpanOfSymbol(signing_node);
                  if (signing_text.find("packed") != std::string_view::npos) {
                    info.is_packed = true;
                  }
                }
              }
              
              // Extract struct fields from child 2
              const verible::Symbol* brace_group = GetSubtreeAsSymbol(prim_child_node, NodeEnum::kStructType, 2);
              if (brace_group && brace_group->Kind() == verible::SymbolKind::kNode) {
                const auto& brace_node = verible::SymbolCastToNode(*brace_group);
                if (brace_node.MatchesTag(NodeEnum::kBraceGroup) && brace_node.size() > 1) {
                  const verible::Symbol* member_list = brace_node[1].get();
                  if (member_list && member_list->Kind() == verible::SymbolKind::kNode) {
                    const auto& member_list_node = verible::SymbolCastToNode(*member_list);
                    if (member_list_node.MatchesTag(NodeEnum::kStructUnionMemberList)) {
                      for (const auto& child : member_list_node.children()) {
                        if (child && child->Kind() == verible::SymbolKind::kNode) {
                          const auto& child_node = verible::SymbolCastToNode(*child);
                          if (child_node.MatchesTag(NodeEnum::kStructUnionMember)) {
                            info.struct_field_count++;
                            // Extract field name from child 1 -> child 2 (Leaf)
                            const verible::Symbol* field_dims = GetSubtreeAsSymbol(child_node, NodeEnum::kStructUnionMember, 1);
                            if (field_dims && field_dims->Kind() == verible::SymbolKind::kNode) {
                              const auto& dims_node = verible::SymbolCastToNode(*field_dims);
                              if (dims_node.MatchesTag(NodeEnum::kDataTypeImplicitIdDimensions)) {
                                const verible::Symbol* id = GetSubtreeAsSymbol(dims_node, NodeEnum::kDataTypeImplicitIdDimensions, 2);
                                if (id && id->Kind() == verible::SymbolKind::kLeaf) {
                                  const auto& id_leaf = verible::SymbolCastToLeaf(*id);
                                  info.struct_field_names.push_back(std::string(id_leaf.get().text()));
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            // Check for union type
            else if (prim_child_node.MatchesTag(NodeEnum::kUnionType)) {
              info.is_union = true;
              info.base_type = "union";
              
              // Check for packed keyword at child 2 (union has optional "tagged" at child 1)
              const verible::Symbol* signing = GetSubtreeAsSymbol(prim_child_node, NodeEnum::kUnionType, 2);
              if (signing && signing->Kind() == verible::SymbolKind::kNode) {
                const auto& signing_node = verible::SymbolCastToNode(*signing);
                if (signing_node.MatchesTag(NodeEnum::kPackedSigning)) {
                  std::string_view signing_text = verible::StringSpanOfSymbol(signing_node);
                  if (signing_text.find("packed") != std::string_view::npos) {
                    info.is_packed = true;
                  }
                }
              }
              
              // Count union members from child 3
              const verible::Symbol* brace_group = GetSubtreeAsSymbol(prim_child_node, NodeEnum::kUnionType, 3);
              if (brace_group && brace_group->Kind() == verible::SymbolKind::kNode) {
                const auto& brace_node = verible::SymbolCastToNode(*brace_group);
                if (brace_node.MatchesTag(NodeEnum::kBraceGroup) && brace_node.size() > 1) {
                  const verible::Symbol* member_list = brace_node[1].get();
                  if (member_list && member_list->Kind() == verible::SymbolKind::kNode) {
                    const auto& member_list_node = verible::SymbolCastToNode(*member_list);
                    if (member_list_node.MatchesTag(NodeEnum::kStructUnionMemberList)) {
                      for (const auto& child : member_list_node.children()) {
                        if (child && child->Kind() == verible::SymbolKind::kNode) {
                          const auto& child_node = verible::SymbolCastToNode(*child);
                          if (child_node.MatchesTag(NodeEnum::kStructUnionMember)) {
                            info.union_member_count++;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            // Check for typedef reference (kUnqualifiedId)
            else if (prim_child_node.MatchesTag(NodeEnum::kUnqualifiedId)) {
              std::string_view id_text = verible::StringSpanOfSymbol(prim_child_node);
              info.base_type = std::string(id_text);
            }
          }
        }
        // Handle `kUnqualifiedId` directly (typedef referencing another typedef)
        else if (base_node.MatchesTag(NodeEnum::kUnqualifiedId)) {
          // This is a typedef reference (e.g., typedef byte_t small_t;)
          std::string_view id_text = verible::StringSpanOfSymbol(base_node);
          info.base_type = std::string(id_text);
        }
        // Handle `kLocalRoot` -> `kUnqualifiedId` (alternate structure)
        else if (base_node.MatchesTag(NodeEnum::kLocalRoot)) {
          const verible::Symbol* unqual_id = GetSubtreeAsSymbol(base_node, NodeEnum::kLocalRoot, 0);
          if (unqual_id && unqual_id->Kind() == verible::SymbolKind::kNode) {
            const auto& unqual_id_node = verible::SymbolCastToNode(*unqual_id);
            if (unqual_id_node.MatchesTag(NodeEnum::kUnqualifiedId)) {
              std::string_view id_text = verible::StringSpanOfSymbol(unqual_id_node);
              info.base_type = std::string(id_text);
            }
          }
        }
      }
    }
    
    // Build resolved type string with dimensions
    if (!info.base_type.empty()) {
      if (info.is_enum) {
        info.resolved_type_string = "enum " + info.base_type;
        if (!info.dimension_string.empty()) {
          info.resolved_type_string += " " + info.dimension_string;
        }
      } else if (info.is_struct) {
        info.resolved_type_string = info.is_packed ? "struct packed" : "struct";
      } else if (info.is_union) {
        info.resolved_type_string = info.is_packed ? "union packed" : "union";
      } else {
        info.resolved_type_string = info.base_type;
        if (!info.dimension_string.empty()) {
          info.resolved_type_string += " " + info.dimension_string;
        }
      }
    }
    
    // Count packed dimensions for array detection and extract dimension_sizes
    if (!info.dimension_string.empty()) {
      size_t dim_count = 0;
      size_t pos = 0;
      while ((pos = info.dimension_string.find('[', pos)) != std::string::npos) {
        dim_count++;
        // Extract size for this dimension
        size_t end_pos = info.dimension_string.find(']', pos);
        if (end_pos != std::string::npos) {
          std::string dim_text = info.dimension_string.substr(pos + 1, end_pos - pos - 1);
          size_t colon = dim_text.find(':');
          if (colon != std::string::npos) {
            try {
              int msb = std::stoi(dim_text.substr(0, colon));
              int lsb = std::stoi(dim_text.substr(colon + 1));
              int size = std::abs(msb - lsb) + 1;
              info.dimension_sizes.push_back(size);
            } catch (...) {
              // Parameterized dimension
            }
          }
        }
        pos++;
      }
      if (dim_count > 1) {
        info.is_array = true;
        info.array_dimensions = dim_count;
      }
    }
    
    // Check for unpacked dimensions (kDeclarationDimensions at child 3)
    const verible::Symbol* unpacked_dims = GetSubtreeAsSymbol(node, NodeEnum::kTypeDeclaration, 3);
    if (unpacked_dims && unpacked_dims->Kind() == verible::SymbolKind::kNode) {
      const auto& unpacked_node = verible::SymbolCastToNode(*unpacked_dims);
      if (unpacked_node.MatchesTag(NodeEnum::kDeclarationDimensions)) {
        info.is_array = true;
        info.is_packed = false;  // Unpacked arrays
        // Count dimensions
        for (const auto& child : unpacked_node.children()) {
          if (child && child->Kind() == verible::SymbolKind::kNode) {
            const auto& dim_node = verible::SymbolCastToNode(*child);
            if (dim_node.MatchesTag(NodeEnum::kDimensionScalar) || 
                dim_node.MatchesTag(NodeEnum::kDimensionRange)) {
              info.array_dimensions++;
            }
          }
        }
      }
    }
    
    // Store in table
    typedef_table[typedef_name] = info;
  }
  
  // Phase 2: Resolve typedef chains recursively
  std::function<TypedefInfo(const std::string&)> resolve_typedef_chain;
  resolve_typedef_chain = [&](const std::string& name) -> TypedefInfo {
    auto it = typedef_table.find(name);
    if (it == typedef_table.end()) {
      return TypedefInfo();  // Not found
    }
    
    TypedefInfo info = it->second;
    
    // Check if base_type is itself a typedef
    auto base_it = typedef_table.find(info.base_type);
    if (base_it != typedef_table.end() && base_it->first != name) {
      // Recursively resolve the chain
      TypedefInfo resolved = resolve_typedef_chain(info.base_type);
      
      // Copy resolved metadata but preserve our own typedef name
      info.base_type = resolved.base_type;
      info.width = resolved.width;
      info.is_signed = resolved.is_signed;
      info.is_packed = resolved.is_packed;
      info.is_enum = resolved.is_enum;
      info.enum_member_count = resolved.enum_member_count;
      info.is_struct = resolved.is_struct;
      info.struct_field_count = resolved.struct_field_count;
      info.struct_field_names = resolved.struct_field_names;
      info.is_union = resolved.is_union;
      info.union_member_count = resolved.union_member_count;
      info.is_parameterized = resolved.is_parameterized;
      info.is_array = resolved.is_array;
      info.array_dimensions = resolved.array_dimensions;
      info.dimension_sizes = resolved.dimension_sizes;
      info.dimension_string = resolved.dimension_string;
      info.resolution_depth = resolved.resolution_depth + 1;
      
      // Rebuild resolved_type_string based on final metadata
      if (info.is_enum) {
        info.resolved_type_string = "enum " + info.base_type;
        if (!info.dimension_string.empty()) {
          info.resolved_type_string += " " + info.dimension_string;
        }
      } else if (info.is_struct) {
        info.resolved_type_string = info.is_packed ? "struct packed" : "struct";
      } else if (info.is_union) {
        info.resolved_type_string = info.is_packed ? "union packed" : "union";
      } else {
        info.resolved_type_string = info.base_type;
        if (!info.dimension_string.empty()) {
          info.resolved_type_string += " " + info.dimension_string;
        }
      }
    }
    
    return info;
  };
  
  // Apply resolution to all typedefs
  for (auto& [name, info] : typedef_table) {
    typedef_table[name] = resolve_typedef_chain(name);
  }
  
  return typedef_table;
}  // End BuildTypedefTable

// Helper: Add type resolution metadata to kDataDeclaration nodes (Phase A)
static void AddTypeResolutionMetadata(
    json &node_json,
    const verible::SyntaxTreeNode &node,
    const std::unordered_map<std::string, TypedefInfo>& typedef_table,
    std::string_view source_text) {
  
  json type_info = json::object();
  
  // Step 1: Get the kInstantiationBase child
  const verible::Symbol* inst_base = GetSubtreeAsSymbol(node, NodeEnum::kDataDeclaration, 1);
  if (!inst_base || inst_base->Kind() != verible::SymbolKind::kNode) {
    return;
  }
  
  const auto& inst_base_node = verible::SymbolCastToNode(*inst_base);
  if (!inst_base_node.MatchesTag(NodeEnum::kInstantiationBase)) {
    return;
  }
  
  // Step 2: Get kDataType (child 0 of kInstantiationBase)
  const verible::Symbol* data_type = GetSubtreeAsSymbol(inst_base_node, NodeEnum::kInstantiationBase, 0);
  if (!data_type) {
    return;
  }
  
  // Step 3: Extract declared type name
  std::string_view declared_type_text = verible::StringSpanOfSymbol(*data_type);
  std::string declared_type(declared_type_text);
  
  // Remove whitespace
  declared_type.erase(std::remove_if(declared_type.begin(), declared_type.end(), ::isspace), declared_type.end());
  
  type_info["declared_type"] = declared_type;
  
  // Step 4: Check for package-scoped types (e.g., my_pkg::word_t)
  bool is_package_scoped = false;
  std::string package_name;
  std::string unqualified_name = declared_type;
  
  size_t scope_pos = declared_type.find("::");
  if (scope_pos != std::string::npos) {
    is_package_scoped = true;
    package_name = declared_type.substr(0, scope_pos);
    unqualified_name = declared_type.substr(scope_pos + 2);
    type_info["is_package_scoped"] = true;
    type_info["package_name"] = package_name;
  }
  
  // Step 5: Look up in typedef table
  auto it = typedef_table.find(is_package_scoped ? unqualified_name : declared_type);
  
  if (it != typedef_table.end()) {
    // Found in typedef table
    const TypedefInfo& info = it->second;
    
    type_info["is_typedef"] = true;
    type_info["resolved_type"] = info.resolved_type_string;
    type_info["base_type"] = info.base_type;
    type_info["width"] = info.width;
    type_info["signed"] = info.is_signed;
    type_info["packed"] = info.is_packed;
    type_info["is_parameterized"] = info.is_parameterized;
    type_info["is_array"] = info.is_array;
    type_info["array_dimensions"] = info.array_dimensions;
    type_info["resolution_depth"] = info.resolution_depth;
    
    // Add definition location
    if (info.definition_line > 0) {
      type_info["definition_location"] = {
        {"line", info.definition_line},
        {"column", info.definition_column}
      };
    }
    
    // Detect forward reference: usage location < definition location
    bool is_forward_ref = false;
    if (info.definition_line > 0) {
      // Extract usage location
      std::string_view usage_text = verible::StringSpanOfSymbol(node);
      if (!source_text.empty() && usage_text.data() >= source_text.data() &&
          usage_text.data() < source_text.data() + source_text.size()) {
        size_t offset = usage_text.data() - source_text.data();
        int usage_line = 1;
        for (size_t i = 0; i < offset && i < source_text.size(); ++i) {
          if (source_text[i] == '\n') {
            usage_line++;
          }
        }
        // Forward reference if usage comes before definition
        is_forward_ref = (usage_line < info.definition_line);
      }
    }
    type_info["is_forward_reference"] = is_forward_ref;
    
    // Add dimension sizes
    if (!info.dimension_sizes.empty()) {
      json dims = json::array();
      for (int size : info.dimension_sizes) {
        dims.push_back(size);
      }
      type_info["dimension_sizes"] = dims;
    }
    
    // Add enum metadata
    if (info.is_enum) {
      type_info["is_enum"] = true;
      type_info["enum_member_count"] = info.enum_member_count;
    }
    
    // Add struct metadata
    if (info.is_struct) {
      type_info["is_struct"] = true;
      type_info["struct_field_count"] = info.struct_field_count;
      if (!info.struct_field_names.empty()) {
        json fields = json::array();
        for (const auto& field : info.struct_field_names) {
          json field_obj = json::object();
          field_obj["name"] = field;
          fields.push_back(field_obj);
        }
        type_info["struct_fields"] = fields;
      }
    }
    
    // Add union metadata
    if (info.is_union) {
      type_info["is_union"] = true;
      type_info["union_member_count"] = info.union_member_count;
    }
  } else {
    // Not found in typedef table
    type_info["is_typedef"] = false;
    
    // Check if it's a built-in type
    static const std::vector<std::string> builtin_types = {
      "logic", "bit", "byte", "shortint", "int", "longint", "integer",
      "reg", "wire", "time", "real", "realtime", "shortreal", "string"
    };
    
    bool is_builtin = false;
    for (const auto& builtin : builtin_types) {
      if (declared_type.find(builtin) != std::string::npos) {
        is_builtin = true;
        type_info["base_type"] = builtin;
        break;
      }
    }
    
    if (!is_builtin) {
      // Unresolved typedef (might be forward reference or package import issue)
      type_info["is_unresolved"] = true;
      type_info["is_forward_reference"] = true;  // Placeholder - true detection needs symbol table
    }
  }
  
  // Add type_info to metadata
  if (!node_json.contains("metadata")) {
    node_json["metadata"] = json::object();
  }
  node_json["metadata"]["type_info"] = type_info;
}  // End AddTypeResolutionMetadata

// Helper: Add cross-reference metadata (Phase B)
static void AddCrossReferenceMetadata(
    json &node_json,
    const verible::Symbol &symbol,
    const std::unordered_map<std::string, SymbolInfo>& symbol_table,
    std::string_view source_text,
    const std::string& current_symbol) {
  
  // Skip empty symbols
  if (current_symbol.empty()) return;
  
  // Look up symbol in table
  auto it = symbol_table.find(current_symbol);
  if (it == symbol_table.end()) {
    // Symbol not found in table - might be undefined or external
    return;
  }
  
  const SymbolInfo& info = it->second;
  
  // Calculate current location
  int current_line = CalculateLineNumber(symbol, source_text);
  int current_column = CalculateColumnNumber(symbol, source_text);
  
  // Determine if this is definition or usage
  bool is_definition = (current_line == info.definition_line && 
                       current_column == info.definition_column);
  
  // Check if this is a redeclaration
  bool is_redeclaration = false;
  for (size_t i = 0; i < info.redeclaration_lines.size(); ++i) {
    if (current_line == info.redeclaration_lines[i] && 
        current_column == info.redeclaration_columns[i]) {
      is_redeclaration = true;
      is_definition = true;  // Redeclarations are also definitions
      break;
    }
  }
  
  // Determine if this is a forward reference (usage before definition)
  bool is_forward_ref = false;
  if (!is_definition && info.has_definition) {
    is_forward_ref = (current_line < info.definition_line);
  }
  
  // Build cross_ref metadata
  json cross_ref = json::object();
  cross_ref["symbol"] = current_symbol;
  cross_ref["ref_type"] = is_definition ? "definition" : "usage";
  
  // Add forward reference flag for usages
  if (!is_definition) {
    cross_ref["is_forward_reference"] = is_forward_ref;
  }
  
  // Add definition location
  if (info.has_definition) {
    cross_ref["definition_location"] = {
      {"line", info.definition_line},
      {"column", info.definition_column}
    };
  }
  
  // Add symbol type info
  cross_ref["symbol_type"] = info.symbol_type;
  
  // Add port-specific metadata
  if (info.is_port) {
    cross_ref["is_port"] = true;
    cross_ref["port_direction"] = info.port_direction;
    cross_ref["is_input"] = (info.port_direction == "input");
    cross_ref["is_output"] = (info.port_direction == "output");
    cross_ref["is_inout"] = (info.port_direction == "inout");
  }
  
  // Add parameter-specific metadata
  if (info.is_parameter) {
    cross_ref["is_parameter"] = true;
  }
  
  // Add usage count for definitions
  if (is_definition) {
    cross_ref["usage_count"] = static_cast<int>(info.usage_lines.size());
  }
  
  // Add redeclaration flag
  if (is_redeclaration) {
    cross_ref["is_redeclaration"] = true;
  }
  
  // Add to node JSON
  if (!node_json.contains("metadata")) {
    node_json["metadata"] = json::object();
  }
  node_json["metadata"]["cross_ref"] = cross_ref;
}  // End AddCrossReferenceMetadata

// Helper method: Add metadata for always blocks (behavioral semantics)
static void AddAlwaysBlockMetadata(json &node_json,
                                    const verible::SyntaxTreeNode &node) {
  json metadata = json::object();
  
  // 1. Detect block type from keyword
  std::string block_type = "always";  // default
  if (node.size() > 0 && node[0]) {
    if (node[0]->Kind() == verible::SymbolKind::kLeaf) {
      const auto &keyword = verible::SymbolCastToLeaf(*node[0]);
      verilog_tokentype token = static_cast<verilog_tokentype>(keyword.get().token_enum());
      
      if (token == TK_always_ff) block_type = "always_ff";
      else if (token == TK_always_comb) block_type = "always_comb";
      else if (token == TK_always_latch) block_type = "always_latch";
    }
  }
  metadata["block_type"] = block_type;
  
  // 2. Extract sensitivity list and detect sequential/combinational
  json sensitivity = json::object();
  json signals = json::array();
  bool is_sequential = false;
  bool has_edge = false;
  std::string clock_signal;
  std::string clock_edge;
  std::string reset_signal;
  std::string reset_edge;
  
  // Get procedural timing control (event control)
  const auto *timing_ctrl = GetProceduralTimingControlFromAlways(node);
  if (timing_ctrl) {
    const auto *event_ctrl = GetEventControlFromProceduralTimingControl(*timing_ctrl);
    
    if (event_ctrl && event_ctrl->Kind() == verible::SymbolKind::kNode) {
      const auto &event_node = verible::down_cast<const verible::SyntaxTreeNode &>(*event_ctrl);
      
      // Check for '@*' or '@(*)' (implicit sensitivity)
      bool found_star = false;
      std::function<bool(const verible::Symbol&)> find_star;
      find_star = [&](const verible::Symbol &sym) -> bool {
        if (sym.Kind() == verible::SymbolKind::kLeaf) {
          const auto &leaf = verible::down_cast<const verible::SyntaxTreeLeaf &>(sym);
          if (leaf.get().text() == "*") {
            found_star = true;
            return true;
          }
        } else if (sym.Kind() == verible::SymbolKind::kNode) {
          const auto &n = verible::down_cast<const verible::SyntaxTreeNode &>(sym);
          for (const auto &child : n.children()) {
            if (child && find_star(*child)) return true;
          }
        }
        return false;
      };
      find_star(event_node);
      
      if (found_star) {
        sensitivity["type"] = "implicit";
      } else {
        // Parse explicit sensitivity list
        sensitivity["type"] = "explicit";
        
        // Traverse to find event expressions (posedge/negedge signals)
        std::string pending_edge;  // Track edge keyword for next identifier
        
        std::function<void(const verible::Symbol&)> extract_events;
        extract_events = [&](const verible::Symbol &sym) {
          if (sym.Kind() == verible::SymbolKind::kLeaf) {
            const auto &leaf = verible::down_cast<const verible::SyntaxTreeLeaf &>(sym);
            verilog_tokentype token = static_cast<verilog_tokentype>(leaf.get().token_enum());
            std::string text(leaf.get().text());
            
            if (token == TK_posedge || text == "posedge") {
              pending_edge = "posedge";
            } else if (token == TK_negedge || text == "negedge") {
              pending_edge = "negedge";
            } else if (verilog::IsIdentifierLike(token)) {
              if (!pending_edge.empty()) {
                // This is a signal with an edge
                json signal = json::object();
                signal["name"] = text;
                signal["edge"] = pending_edge;
                signals.push_back(signal);
                
                has_edge = true;
                is_sequential = true;
                
                // First edge signal is clock
                if (clock_signal.empty()) {
                  clock_signal = text;
                  clock_edge = pending_edge;
                } else if (reset_signal.empty()) {
                  // Second edge signal is async reset
                  reset_signal = text;
                  reset_edge = pending_edge;
                }
                
                pending_edge.clear();  // Reset for next signal
              } else {
                // Level-sensitive signal (no edge keyword)
                json signal = json::object();
                signal["name"] = text;
                signal["edge"] = "level";
                signals.push_back(signal);
              }
            }
          } else if (sym.Kind() == verible::SymbolKind::kNode) {
            const auto &n = verible::down_cast<const verible::SyntaxTreeNode &>(sym);
            for (const auto &child : n.children()) {
              if (child) extract_events(*child);
            }
          }
        };
        
        extract_events(event_node);
        
        if (has_edge) {
          sensitivity["type"] = "edge";
        }
      }
    }
  } else {
    // No event control (always_comb, always_latch without @)
    sensitivity["type"] = "implicit";
  }
  
  sensitivity["signals"] = signals;
  metadata["sensitivity"] = sensitivity;
  
  // 3. Sequential vs. Combinational
  metadata["is_sequential"] = is_sequential;
  metadata["is_combinational"] = (block_type == "always_comb") || 
                                  (!is_sequential && block_type != "always_latch");
  
  // 4. Clock info (if sequential)
  if (is_sequential && !clock_signal.empty()) {
    json clock_info = json::object();
    clock_info["signal"] = clock_signal;
    clock_info["edge"] = clock_edge;
    metadata["clock_info"] = clock_info;
  }
  
  // 5. Reset info (if async reset detected OR sync reset in body)
  if (!reset_signal.empty()) {
    // Async reset (from sensitivity list)
    json reset_info = json::object();
    reset_info["signal"] = reset_signal;
    reset_info["type"] = "async";
    reset_info["active"] = (reset_edge == "negedge") ? "low" : "high";
    reset_info["edge"] = reset_edge;
    metadata["reset_info"] = reset_info;
  } else if (is_sequential) {
    // Try to detect synchronous reset from first if-statement in body
    std::string sync_reset_signal;
    bool sync_reset_active_high = true;
    
    std::function<bool(const verible::Symbol&)> find_first_if;
    find_first_if = [&](const verible::Symbol &sym) -> bool {
      if (sym.Kind() == verible::SymbolKind::kNode) {
        const auto &n = verible::down_cast<const verible::SyntaxTreeNode &>(sym);
        NodeEnum tag = static_cast<NodeEnum>(n.Tag().tag);
        
        if (tag == NodeEnum::kIfClause || tag == NodeEnum::kIfHeader) {
          // Found an if - try to extract the condition
          // Look for identifier in condition
          bool negation_seen = false;
          std::function<void(const verible::Symbol&)> extract_reset_signal;
          extract_reset_signal = [&](const verible::Symbol &s) {
            if (s.Kind() == verible::SymbolKind::kLeaf) {
              const auto &leaf = verible::down_cast<const verible::SyntaxTreeLeaf &>(s);
              verilog_tokentype token = static_cast<verilog_tokentype>(leaf.get().token_enum());
              std::string text(leaf.get().text());
              
              if (text == "!" || text == "~") {
                // Negation found - next identifier will be active low
                negation_seen = true;
                sync_reset_active_high = false;
              } else if (verilog::IsIdentifierLike(token) && sync_reset_signal.empty()) {
                // Only consider this as a reset signal if it matches reset patterns
                // and does NOT match enable patterns (to avoid false positives)
                if (IsLikelyResetSignal(text) && !IsLikelyEnableSignal(text)) {
                  sync_reset_signal = text;
                  // Use negation_seen flag to determine active level
                  if (!negation_seen) {
                    sync_reset_active_high = true;  // No negation = active high
                  }
                  // If negation_seen is true, sync_reset_active_high is already false
                }
              }
            } else if (s.Kind() == verible::SymbolKind::kNode) {
              const auto &sn = verible::down_cast<const verible::SyntaxTreeNode &>(s);
              for (const auto &child : sn.children()) {
                if (child) extract_reset_signal(*child);
                if (!sync_reset_signal.empty()) break;  // Found it
              }
            }
          };
          
          extract_reset_signal(n);
          return true;  // Stop searching
        }
        
        // Continue searching in children
        for (const auto &child : n.children()) {
          if (child && find_first_if(*child)) return true;
        }
      }
      return false;
    };
    
    find_first_if(node);
    
    if (!sync_reset_signal.empty()) {
      json reset_info = json::object();
      reset_info["signal"] = sync_reset_signal;
      reset_info["type"] = "sync";
      reset_info["active"] = sync_reset_active_high ? "high" : "low";
      reset_info["edge"] = nullptr;
      metadata["reset_info"] = reset_info;
    }
  }
  
  // 6. Assignment type (blocking vs. non-blocking)
  int blocking_count = 0;
  int nonblocking_count = 0;
  
  std::function<void(const verible::Symbol&)> count_assignments;
  count_assignments = [&](const verible::Symbol &sym) {
    if (sym.Kind() == verible::SymbolKind::kNode) {
      const auto &n = verible::down_cast<const verible::SyntaxTreeNode &>(sym);
      NodeEnum tag = static_cast<NodeEnum>(n.Tag().tag);
      
      if (tag == NodeEnum::kBlockingAssignmentStatement || 
          tag == NodeEnum::kNetVariableAssignment) {
        blocking_count++;
      } else if (tag == NodeEnum::kNonblockingAssignmentStatement) {
        nonblocking_count++;
      }
      
      for (const auto &child : n.children()) {
        if (child) count_assignments(*child);
      }
    }
  };
  
  count_assignments(node);
  
  std::string assignment_type;
  if (nonblocking_count > 0 && blocking_count == 0) {
    assignment_type = "nonblocking";
  } else if (blocking_count > 0 && nonblocking_count == 0) {
    assignment_type = "blocking";
  } else if (blocking_count > 0 && nonblocking_count > 0) {
    assignment_type = "mixed";
  } else {
    // Default based on block type
    assignment_type = (block_type == "always_ff") ? "nonblocking" : "blocking";
  }
  metadata["assignment_type"] = assignment_type;
  
  node_json["metadata"] = metadata;
}

class VerilogTreeToJsonConverter : public verible::SymbolVisitor {
 public:
  explicit VerilogTreeToJsonConverter(std::string_view base,
                                     const std::unordered_map<std::string, TypedefInfo>& typedef_table,
                                     const std::unordered_map<std::string, SymbolInfo>& symbol_table);

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

  // Typedef lookup table for type resolution (Phase A)
  const std::unordered_map<std::string, TypedefInfo>& typedef_table_;

  // Symbol table for cross-reference tracking (Phase B)
  const std::unordered_map<std::string, SymbolInfo>& symbol_table_;

  // JSON tree root
  json json_;

  // Pointer to JSON value of currently visited symbol in its parent's
  // children list.
  json *value_;
};

VerilogTreeToJsonConverter::VerilogTreeToJsonConverter(std::string_view base,
                                                       const std::unordered_map<std::string, TypedefInfo>& typedef_table,
                                                       const std::unordered_map<std::string, SymbolInfo>& symbol_table)
    : context_(base,
               [](std::ostream &stream, int e) {
                 stream << TokenTypeToString(static_cast<verilog_tokentype>(e));
               }),
      typedef_table_(typedef_table),
      symbol_table_(symbol_table),
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
  
  // Add location metadata
  if (!context_.base.empty()) {
    (*value_)["location"] = AddLocationMetadata(leaf, context_.base);
  }
}

void VerilogTreeToJsonConverter::Visit(const verible::SyntaxTreeNode &node) {
  *value_ = json::object();
  (*value_)["tag"] = NodeEnumToString(static_cast<NodeEnum>(node.Tag().tag));
  
  // Add location metadata
  if (!context_.base.empty()) {
    (*value_)["location"] = AddLocationMetadata(node, context_.base);
  }
  
  // Extract and include the full source text for this node
  std::string_view node_text = verible::StringSpanOfSymbol(node);
  if (!node_text.empty()) {
    (*value_)["text"] = std::string(node_text);
  }
  
  // Add metadata for supported node types
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
  } else if (tag == NodeEnum::kModuleDeclaration) {
    // Phase C: Add scope metadata for modules
    // Extract module name from node structure
    auto name_matches = verible::SearchSyntaxTree(node, NodekUnqualifiedId());
    if (!name_matches.empty() && name_matches[0].match) {
      std::string_view mod_name = verible::StringSpanOfSymbol(*name_matches[0].match);
      
      json scope_info = json::object();
      scope_info["scope_type"] = "module";
      scope_info["scope_name"] = std::string(mod_name);
      
      if (!value_->contains("metadata")) {
        (*value_)["metadata"] = json::object();
      }
      (*value_)["metadata"]["scope_info"] = scope_info;
    }
  } else if (tag == NodeEnum::kFunctionDeclaration || tag == NodeEnum::kTaskDeclaration) {
    // Phase C: Add scope metadata for functions/tasks
    auto name_matches = verible::SearchSyntaxTree(node, NodekUnqualifiedId());
    if (!name_matches.empty() && name_matches[0].match) {
      std::string_view func_name = verible::StringSpanOfSymbol(*name_matches[0].match);
      
      json scope_info = json::object();
      scope_info["scope_type"] = (tag == NodeEnum::kFunctionDeclaration) ? "function" : "task";
      scope_info["scope_name"] = std::string(func_name);
      
      if (!value_->contains("metadata")) {
        (*value_)["metadata"] = json::object();
      }
      (*value_)["metadata"]["scope_info"] = scope_info;
    }
  } else if (tag == NodeEnum::kNetVariableAssignment || tag == NodeEnum::kBlockingAssignmentStatement || tag == NodeEnum::kNonblockingAssignmentStatement) {
    // Phase D: Add dataflow metadata for assignments
    std::string driver_type = "unknown";
    if (tag == NodeEnum::kNetVariableAssignment) {
      driver_type = "continuous";
    } else if (tag == NodeEnum::kBlockingAssignmentStatement) {
      driver_type = "blocking";
    } else if (tag == NodeEnum::kNonblockingAssignmentStatement) {
      driver_type = "nonblocking";
    }
    
    // Extract target signal from LHS
    // Child 0 is typically the LHS
    if (node.size() > 0 && node[0]) {
      std::string_view lhs_text = verible::StringSpanOfSymbol(*node[0]);
      
      json dataflow_info = json::object();
      dataflow_info["has_driver"] = true;
      dataflow_info["driver_type"] = driver_type;
      dataflow_info["target_signal"] = std::string(lhs_text);
      
      if (!value_->contains("metadata")) {
        (*value_)["metadata"] = json::object();
      }
      (*value_)["metadata"]["dataflow_info"] = dataflow_info;
    }
  } else if (tag == NodeEnum::kAlwaysStatement) {
    AddAlwaysBlockMetadata(*value_, node);  // Phase 4: Behavioral metadata
  } else if (tag == NodeEnum::kAssertionStatement || 
             tag == NodeEnum::kAssumeStatement || 
             tag == NodeEnum::kCoverStatement) {
    // Phase SVA-1: Immediate Assertions
    // Add basic assertion metadata
    json assertion_info = json::object();
    
    std::string assertion_type;
    if (tag == NodeEnum::kAssertionStatement) {
      assertion_type = "assert";
    } else if (tag == NodeEnum::kAssumeStatement) {
      assertion_type = "assume";
    } else {
      assertion_type = "cover";
    }
    
    assertion_info["assertion_type"] = assertion_type;
    
    // Extract assertion condition from the clause/header structure
    // Structure: kAssertionStatement -> kAssertionClause -> kAssertionHeader -> expression
    if (node.size() > 0 && node[0]) {
      const auto* clause = node[0].get();
      if (clause && clause->Kind() == verible::SymbolKind::kNode) {
        const auto& clause_node = verible::SymbolCastToNode(*clause);
        if (clause_node.size() > 0 && clause_node[0]) {
          const auto* header = clause_node[0].get();
          if (header && header->Kind() == verible::SymbolKind::kNode) {
            const auto& header_node = verible::SymbolCastToNode(*header);
            // Header contains: keyword, timing (optional), paren group with expression
            // Try to extract the condition expression
            for (size_t i = 0; i < header_node.size(); i++) {
              if (header_node[i] && header_node[i]->Kind() == verible::SymbolKind::kNode) {
                const auto& child = verible::SymbolCastToNode(*header_node[i]);
                // Look for paren group or expression
                std::string_view expr_text = verible::StringSpanOfSymbol(child);
                if (!expr_text.empty() && expr_text.find('(') != std::string_view::npos) {
                  assertion_info["condition"] = std::string(expr_text);
                  break;
                }
              }
            }
          }
        }
        
        // Check if there's an action block (else clause)
        if (clause_node.size() > 1 && clause_node[1]) {
          assertion_info["has_action_block"] = true;
        } else {
          assertion_info["has_action_block"] = false;
        }
      }
    }
    
    // Check for else clause (failure action)
    if (node.size() > 1 && node[1]) {
      assertion_info["has_else_clause"] = true;
    } else {
      assertion_info["has_else_clause"] = false;
    }
    
    if (!value_->contains("metadata")) {
      (*value_)["metadata"] = json::object();
    }
    (*value_)["metadata"]["assertion_info"] = assertion_info;
  } else if (tag == NodeEnum::kPropertyDeclaration) {
    // Phase SVA-2: Property Declarations
    json property_info = json::object();
    property_info["construct_type"] = "property_declaration";
    
    // Extract property name - typically at child 1
    if (node.size() > 1 && node[1]) {
      std::string_view prop_name = verible::StringSpanOfSymbol(*node[1]);
      property_info["property_name"] = std::string(prop_name);
    }
    
    if (!value_->contains("metadata")) {
      (*value_)["metadata"] = json::object();
    }
    (*value_)["metadata"]["property_info"] = property_info;
  } else if (tag == NodeEnum::kAssertPropertyStatement || 
             tag == NodeEnum::kAssumePropertyStatement ||
             tag == NodeEnum::kCoverPropertyStatement ||
             tag == NodeEnum::kExpectPropertyStatement ||
             tag == NodeEnum::kRestrictPropertyStatement) {
    // Phase SVA-2: Concurrent Assertion Statements
    json concurrent_assertion = json::object();
    
    std::string assertion_type;
    if (tag == NodeEnum::kAssertPropertyStatement) {
      assertion_type = "assert_property";
    } else if (tag == NodeEnum::kAssumePropertyStatement) {
      assertion_type = "assume_property";
    } else if (tag == NodeEnum::kCoverPropertyStatement) {
      assertion_type = "cover_property";
    } else if (tag == NodeEnum::kExpectPropertyStatement) {
      assertion_type = "expect_property";
    } else {
      assertion_type = "restrict_property";
    }
    
    concurrent_assertion["assertion_type"] = assertion_type;
    concurrent_assertion["is_concurrent"] = true;
    
    if (!value_->contains("metadata")) {
      (*value_)["metadata"] = json::object();
    }
    (*value_)["metadata"]["concurrent_assertion_info"] = concurrent_assertion;
  } else if (tag == NodeEnum::kSequenceDeclaration) {
    // Phase SVA-3: Sequence Declarations
    json sequence_info = json::object();
    sequence_info["construct_type"] = "sequence_declaration";
    
    // Extract sequence name - typically at child 1
    if (node.size() > 1 && node[1]) {
      std::string_view seq_name = verible::StringSpanOfSymbol(*node[1]);
      sequence_info["sequence_name"] = std::string(seq_name);
    }
    
    if (!value_->contains("metadata")) {
      (*value_)["metadata"] = json::object();
    }
    (*value_)["metadata"]["sequence_info"] = sequence_info;
  } else if (tag == NodeEnum::kCoverSequenceStatement) {
    // Phase SVA-3: Cover Sequence Statements
    json cover_sequence = json::object();
    cover_sequence["assertion_type"] = "cover_sequence";
    cover_sequence["is_concurrent"] = true;
    
    if (!value_->contains("metadata")) {
      (*value_)["metadata"] = json::object();
    }
    (*value_)["metadata"]["concurrent_assertion_info"] = cover_sequence;
  } else if (tag == NodeEnum::kDPIImportItem) {
    // Phase DPI-1: DPI-C Import
    json dpi_info = json::object();
    dpi_info["direction"] = "import";
    dpi_info["spec"] = "DPI-C";
    
    // Extract spec string (child 1 - should be "DPI-C")
    if (node.size() > 1 && node[1]) {
      std::string_view spec_str = verible::StringSpanOfSymbol(*node[1]);
      // Remove quotes from "DPI-C"
      if (!spec_str.empty() && spec_str.front() == '"' && spec_str.back() == '"') {
        spec_str = spec_str.substr(1, spec_str.size() - 2);
      }
      dpi_info["spec"] = std::string(spec_str);
    }
    
    // Check for context or pure modifiers (child 2)
    dpi_info["is_context"] = false;
    dpi_info["is_pure"] = false;
    if (node.size() > 2 && node[2]) {
      std::string_view modifier = verible::StringSpanOfSymbol(*node[2]);
      if (modifier.find("context") != std::string_view::npos) {
        dpi_info["is_context"] = true;
      }
      if (modifier.find("pure") != std::string_view::npos) {
        dpi_info["is_pure"] = true;
      }
    }
    
    // Determine if it's a task or function by checking for kTaskPrototype child
    dpi_info["is_task"] = false;
    for (size_t i = 0; i < node.size(); i++) {
      if (node[i] && node[i]->Kind() == verible::SymbolKind::kNode) {
        const auto& child_node = verible::SymbolCastToNode(*node[i]);
        if (static_cast<verilog::NodeEnum>(child_node.Tag().tag) == NodeEnum::kTaskPrototype) {
          dpi_info["is_task"] = true;
          break;
        }
      }
    }
    
    // Extract function/task name and return type from prototype
    // The prototype structure varies, so we extract from the text
    std::string_view full_text = verible::StringSpanOfSymbol(node);
    
    // Try to find function/task name (identifier after "function" or "task")
    size_t func_pos = full_text.find("function");
    size_t task_pos = full_text.find("task");
    size_t keyword_pos = (func_pos != std::string_view::npos) ? func_pos : task_pos;
    
    if (keyword_pos != std::string_view::npos) {
      // Skip past "function" or "task"
      size_t start = full_text.find_first_not_of(" \t", keyword_pos + (func_pos != std::string_view::npos ? 8 : 4));
      
      // Find the identifier (function/task name) - look for the part before '('
      size_t paren_pos = full_text.find('(', start);
      if (paren_pos != std::string_view::npos) {
        // Work backwards from '(' to find the identifier
        size_t name_end = full_text.find_last_not_of(" \t", paren_pos - 1);
        if (name_end != std::string_view::npos) {
          size_t name_start = full_text.find_last_of(" \t", name_end);
          if (name_start != std::string_view::npos) {
            std::string_view func_name = full_text.substr(name_start + 1, name_end - name_start);
            dpi_info["function_name"] = std::string(func_name);
          }
        }
      }
    }
    
    if (!value_->contains("metadata")) {
      (*value_)["metadata"] = json::object();
    }
    (*value_)["metadata"]["dpi_info"] = dpi_info;
  } else if (tag == NodeEnum::kDPIExportItem) {
    // Phase DPI-1: DPI-C Export
    json dpi_info = json::object();
    dpi_info["direction"] = "export";
    dpi_info["spec"] = "DPI-C";
    
    // Extract spec string (child 1)
    if (node.size() > 1 && node[1]) {
      std::string_view spec_str = verible::StringSpanOfSymbol(*node[1]);
      // Remove quotes
      if (!spec_str.empty() && spec_str.front() == '"' && spec_str.back() == '"') {
        spec_str = spec_str.substr(1, spec_str.size() - 2);
      }
      dpi_info["spec"] = std::string(spec_str);
    }
    
    // Check if it's a task or function
    dpi_info["is_task"] = false;
    std::string_view full_text = verible::StringSpanOfSymbol(node);
    if (full_text.find("task") != std::string_view::npos) {
      dpi_info["is_task"] = true;
    }
    
    // Extract C linkage name and function name
    // Structure: export "DPI-C" [c_name =] function sv_name;
    // Child[2] = c_name (if present), Child[3] = '=' (if present), Child[4+] = function prototype
    if (node.size() > 3 && node[3] && node[3]->Kind() == verible::SymbolKind::kLeaf) {
      const auto& eq_leaf = verible::SymbolCastToLeaf(*node[3]);
      if (eq_leaf.get().text() == "=") {
        // Extract C linkage name from child[2]
        if (node[2] && node[2]->Kind() == verible::SymbolKind::kLeaf) {
          const auto& c_name_leaf = verible::SymbolCastToLeaf(*node[2]);
          dpi_info["c_linkage_name"] = std::string(c_name_leaf.get().text());
        }
      }
    }
    
    // Extract SV function/task name from the prototype
    // Look for kFunctionPrototype or kTaskPrototype child
    for (size_t i = 0; i < node.size(); i++) {
      if (node[i] && node[i]->Kind() == verible::SymbolKind::kNode) {
        const auto& child_node = verible::SymbolCastToNode(*node[i]);
        auto child_tag = static_cast<verilog::NodeEnum>(child_node.Tag().tag);
        
        if (child_tag == NodeEnum::kFunctionPrototype || child_tag == NodeEnum::kTaskPrototype) {
          // Try to get function/task name from the prototype
          // It's usually in a kUnqualifiedId node within the prototype
          for (size_t j = 0; j < child_node.size(); j++) {
            if (child_node[j] && child_node[j]->Kind() == verible::SymbolKind::kNode) {
              const auto& proto_child = verible::SymbolCastToNode(*child_node[j]);
              if (static_cast<verilog::NodeEnum>(proto_child.Tag().tag) == NodeEnum::kUnqualifiedId) {
                std::string_view func_name = verible::StringSpanOfSymbol(proto_child);
                dpi_info["function_name"] = std::string(func_name);
                break;
              }
            }
          }
          break;
        }
      }
    }
    
    // Fallback: extract from text if not found in CST
    if (!dpi_info.contains("function_name") || dpi_info["function_name"].get<std::string>().empty()) {
      size_t func_pos = full_text.find("function");
      size_t task_pos = full_text.find("task");
      size_t keyword_pos = (func_pos != std::string_view::npos) ? func_pos + 8 : task_pos + 4;
      size_t name_start = full_text.find_first_not_of(" \t", keyword_pos);
      if (name_start != std::string_view::npos) {
        size_t semi_pos = full_text.find(';', name_start);
        if (semi_pos != std::string_view::npos) {
          size_t name_end = full_text.find_last_not_of(" \t;", semi_pos - 1);
          std::string_view func_name = full_text.substr(name_start, name_end - name_start + 1);
          dpi_info["function_name"] = std::string(func_name);
        }
      }
    }
    
    if (!value_->contains("metadata")) {
      (*value_)["metadata"] = json::object();
    }
    (*value_)["metadata"]["dpi_info"] = dpi_info;
  } else if (tag == NodeEnum::kProgramDeclaration) {
    // Phase PROGRAM-1: Program Blocks
    json program_info = json::object();
    
    // Look for kModuleHeader child (child[0])
    if (node.size() > 0 && node[0] && node[0]->Kind() == verible::SymbolKind::kNode) {
      const auto& header = verible::SymbolCastToNode(*node[0]);
      
      // Check for "automatic" or "static" keyword
      program_info["is_automatic"] = false;
      program_info["is_static"] = false;
      
      for (size_t i = 0; i < header.size(); i++) {
        if (header[i] && header[i]->Kind() == verible::SymbolKind::kLeaf) {
          const auto& leaf = verible::SymbolCastToLeaf(*header[i]);
          std::string_view text = leaf.get().text();
          if (text == "automatic") {
            program_info["is_automatic"] = true;
          } else if (text == "static") {
            program_info["is_static"] = true;
          }
        }
      }
      
      // Extract program name - typically child[2] in header
      if (header.size() > 2 && header[2]) {
        std::string_view prog_name = verible::StringSpanOfSymbol(*header[2]);
        program_info["program_name"] = std::string(prog_name);
      }
      
      // Check for ports - look for kParenGroup or kPortDeclarationList
      program_info["has_ports"] = false;
      for (size_t i = 0; i < header.size(); i++) {
        if (header[i] && header[i]->Kind() == verible::SymbolKind::kNode) {
          const auto& child_node = verible::SymbolCastToNode(*header[i]);
          auto child_tag = static_cast<verilog::NodeEnum>(child_node.Tag().tag);
          if (child_tag == NodeEnum::kParenGroup || child_tag == NodeEnum::kPortDeclarationList) {
            program_info["has_ports"] = true;
            break;
          }
        }
      }
    }
    
    // Count program items (initial, final, functions, tasks, etc.)
    int item_count = 0;
    for (size_t i = 1; i < node.size(); i++) {
      if (node[i] && node[i]->Kind() == verible::SymbolKind::kNode) {
        const auto& child_node = verible::SymbolCastToNode(*node[i]);
        auto child_tag = static_cast<verilog::NodeEnum>(child_node.Tag().tag);
        // Count items in kProgramItemList
        if (child_tag == NodeEnum::kModuleItemList) {
          item_count = child_node.size();
          break;
        }
      }
    }
    program_info["item_count"] = item_count;
    
    if (!value_->contains("metadata")) {
      (*value_)["metadata"] = json::object();
    }
    (*value_)["metadata"]["program_info"] = program_info;
  } else if (tag == NodeEnum::kCovergroupDeclaration) {
    // Phase COVERAGE-1: Functional Coverage
    json coverage_info = json::object();
    
    // Look for kCovergroupHeader child (child[0])
    if (node.size() > 0 && node[0] && node[0]->Kind() == verible::SymbolKind::kNode) {
      const auto& header = verible::SymbolCastToNode(*node[0]);
      
      // Extract covergroup name - typically child[1] in header
      if (header.size() > 1 && header[1]) {
        std::string_view cg_name = verible::StringSpanOfSymbol(*header[1]);
        coverage_info["covergroup_name"] = std::string(cg_name);
      }
      
      // Check for trigger event - look for kEventControl
      coverage_info["has_trigger_event"] = false;
      for (size_t i = 0; i < header.size(); i++) {
        if (header[i] && header[i]->Kind() == verible::SymbolKind::kNode) {
          const auto& child_node = verible::SymbolCastToNode(*header[i]);
          auto child_tag = static_cast<verilog::NodeEnum>(child_node.Tag().tag);
          if (child_tag == NodeEnum::kEventControl) {
            coverage_info["has_trigger_event"] = true;
            std::string_view trigger = verible::StringSpanOfSymbol(child_node);
            coverage_info["trigger_event"] = std::string(trigger);
            break;
          }
        }
      }
    }
    
    // Count coverpoints and cross items
    int coverpoint_count = 0;
    int cross_count = 0;
    bool has_options = false;
    
    for (size_t i = 1; i < node.size(); i++) {
      if (node[i] && node[i]->Kind() == verible::SymbolKind::kNode) {
        const auto& child_node = verible::SymbolCastToNode(*node[i]);
        auto child_tag = static_cast<verilog::NodeEnum>(child_node.Tag().tag);
        
        // Count different coverage constructs
        if (child_tag == NodeEnum::kCoverPoint) {
          coverpoint_count++;
        } else if (child_tag == NodeEnum::kCoverCross) {
          cross_count++;
        } else if (child_tag == NodeEnum::kCoverageOption || 
                   child_tag == NodeEnum::kCoverageSpecOptionList) {
          has_options = true;
        }
      }
    }
    
    coverage_info["coverpoint_count"] = coverpoint_count;
    coverage_info["cross_count"] = cross_count;
    coverage_info["has_options"] = has_options;
    
    if (!value_->contains("metadata")) {
      (*value_)["metadata"] = json::object();
    }
    (*value_)["metadata"]["coverage_info"] = coverage_info;
  } else if (tag == NodeEnum::kClassDeclaration) {
    // Phase OOP-1: Class & Object-Oriented Programming
    json class_info = json::object();
    
    // Look for kClassHeader child (child[0])
    if (node.size() > 0 && node[0] && node[0]->Kind() == verible::SymbolKind::kNode) {
      const auto& header = verible::SymbolCastToNode(*node[0]);
      
      // Check for "virtual" modifier at beginning
      class_info["is_virtual"] = false;
      if (header.size() > 0 && header[0] && header[0]->Kind() == verible::SymbolKind::kLeaf) {
        const auto& first_leaf = verible::SymbolCastToLeaf(*header[0]);
        if (first_leaf.get().text() == "virtual") {
          class_info["is_virtual"] = true;
        }
      }
      
      // Extract class name - scan for SymbolIdentifier after "class" keyword
      bool found_class_keyword = false;
      for (size_t i = 0; i < header.size(); i++) {
        if (header[i] && header[i]->Kind() == verible::SymbolKind::kLeaf) {
          const auto& leaf = verible::SymbolCastToLeaf(*header[i]);
          if (leaf.get().text() == "class") {
            found_class_keyword = true;
          } else if (found_class_keyword && leaf.get().token_enum() == verilog_tokentype::SymbolIdentifier) {
            // First identifier after "class" keyword is the class name
            class_info["class_name"] = std::string(leaf.get().text());
            break;
          }
        }
      }
      
      // Check for parent class - look for kExtendsList
      class_info["parent_class"] = nullptr;
      for (size_t i = 0; i < header.size(); i++) {
        if (header[i] && header[i]->Kind() == verible::SymbolKind::kNode) {
          const auto& child_node = verible::SymbolCastToNode(*header[i]);
          auto child_tag = static_cast<verilog::NodeEnum>(child_node.Tag().tag);
          if (child_tag == NodeEnum::kExtendsList) {
            // Parent class name is in kUnqualifiedId within kExtendsList
            if (child_node.size() > 1 && child_node[1] && 
                child_node[1]->Kind() == verible::SymbolKind::kNode) {
              const auto& unqual = verible::SymbolCastToNode(*child_node[1]);
              if (unqual.size() > 0 && unqual[0] && 
                  unqual[0]->Kind() == verible::SymbolKind::kLeaf) {
                const auto& parent_leaf = verible::SymbolCastToLeaf(*unqual[0]);
                class_info["parent_class"] = std::string(parent_leaf.get().text());
              }
            }
            break;
          }
        }
      }
    }
    
    // Count properties and methods in kClassItems
    int property_count = 0;
    int method_count = 0;
    bool constructor_present = false;
    int rand_variable_count = 0;
    bool has_constraints = false;
    
    // Look for kClassItems (child[1])
    if (node.size() > 1 && node[1] && node[1]->Kind() == verible::SymbolKind::kNode) {
      const auto& class_items = verible::SymbolCastToNode(*node[1]);
      
      for (size_t i = 0; i < class_items.size(); i++) {
        if (class_items[i] && class_items[i]->Kind() == verible::SymbolKind::kNode) {
          const auto& item = verible::SymbolCastToNode(*class_items[i]);
          auto item_tag = static_cast<verilog::NodeEnum>(item.Tag().tag);
          
          if (item_tag == NodeEnum::kDataDeclaration) {
            property_count++;
            // Check for rand/randc variables
            std::string_view item_text = verible::StringSpanOfSymbol(item);
            if (item_text.find("rand ") != std::string_view::npos ||
                item_text.find("randc ") != std::string_view::npos) {
              rand_variable_count++;
            }
          } else if (item_tag == NodeEnum::kClassConstructor) {
            constructor_present = true;
          } else if (item_tag == NodeEnum::kFunctionDeclaration) {
            method_count++;
          } else if (item_tag == NodeEnum::kTaskDeclaration) {
            method_count++;
          } else if (item_tag == NodeEnum::kConstraintDeclaration) {
            has_constraints = true;
          }
        }
      }
    }
    
    class_info["property_count"] = property_count;
    class_info["method_count"] = method_count;
    class_info["constructor_present"] = constructor_present;
    class_info["has_constraints"] = has_constraints;
    class_info["rand_variable_count"] = rand_variable_count;
    
    // Placeholder for inheritance chain and depth (requires semantic analysis)
    class_info["inheritance_depth"] = class_info["parent_class"].is_null() ? 0 : 1;
    
    if (!value_->contains("metadata")) {
      (*value_)["metadata"] = json::object();
    }
    (*value_)["metadata"]["class_info"] = class_info;
  } else if (tag == NodeEnum::kInterfaceDeclaration) {
    // Phase 2: Interfaces & Modports
    json interface_info = json::object();
    
    // Look for kModuleHeader child (child[0]) - interfaces use same header structure as modules
    if (node.size() > 0 && node[0] && node[0]->Kind() == verible::SymbolKind::kNode) {
      const auto& header = verible::SymbolCastToNode(*node[0]);
      
      // Extract interface name - scan for SymbolIdentifier after "interface" keyword
      bool found_interface_keyword = false;
      for (size_t i = 0; i < header.size(); i++) {
        if (header[i] && header[i]->Kind() == verible::SymbolKind::kLeaf) {
          const auto& leaf = verible::SymbolCastToLeaf(*header[i]);
          if (leaf.get().text() == "interface") {
            found_interface_keyword = true;
          } else if (found_interface_keyword && leaf.get().token_enum() == verilog_tokentype::SymbolIdentifier) {
            // First identifier after "interface" keyword is the interface name
            interface_info["interface_name"] = std::string(leaf.get().text());
            break;
          }
        }
      }
      
      // Check for parameters in header (look for kFormalParameterListDeclaration)
      interface_info["has_parameters"] = false;
      for (size_t i = 0; i < header.size(); i++) {
        if (header[i] && header[i]->Kind() == verible::SymbolKind::kNode) {
          const auto& child_node = verible::SymbolCastToNode(*header[i]);
          auto child_tag = static_cast<verilog::NodeEnum>(child_node.Tag().tag);
          if (child_tag == NodeEnum::kFormalParameterListDeclaration) {
            interface_info["has_parameters"] = true;
            break;
          }
        }
      }
      
      // Check for ports in header (look for kParenGroup containing kPortDeclarationList)
      interface_info["has_ports"] = false;
      for (size_t i = 0; i < header.size(); i++) {
        if (header[i] && header[i]->Kind() == verible::SymbolKind::kNode) {
          const auto& child_node = verible::SymbolCastToNode(*header[i]);
          auto child_tag = static_cast<verilog::NodeEnum>(child_node.Tag().tag);
          if (child_tag == NodeEnum::kParenGroup) {
            // Check if this ParenGroup contains port declarations
            for (size_t j = 0; j < child_node.size(); j++) {
              if (child_node[j] && child_node[j]->Kind() == verible::SymbolKind::kNode) {
                const auto& paren_child = verible::SymbolCastToNode(*child_node[j]);
                auto paren_child_tag = static_cast<verilog::NodeEnum>(paren_child.Tag().tag);
                if (paren_child_tag == NodeEnum::kPortDeclarationList) {
                  interface_info["has_ports"] = true;
                  break;
                }
              }
            }
            if (interface_info["has_ports"]) break;
          }
        }
      }
    }
    
    // Count signals, modports, and check for clocking blocks in kModuleItemList
    int signal_count = 0;
    int modport_count = 0;
    bool has_clocking_blocks = false;
    std::vector<std::string> modport_names;
    
    // Look for kModuleItemList (child[1])
    if (node.size() > 1 && node[1] && node[1]->Kind() == verible::SymbolKind::kNode) {
      const auto& item_list = verible::SymbolCastToNode(*node[1]);
      
      for (size_t i = 0; i < item_list.size(); i++) {
        if (item_list[i] && item_list[i]->Kind() == verible::SymbolKind::kNode) {
          const auto& item = verible::SymbolCastToNode(*item_list[i]);
          auto item_tag = static_cast<verilog::NodeEnum>(item.Tag().tag);
          
          if (item_tag == NodeEnum::kDataDeclaration) {
            signal_count++;
          } else if (item_tag == NodeEnum::kModportDeclaration) {
            modport_count++;
            
            // Extract modport names from kModportItemList
            if (item.size() > 1 && item[1] && item[1]->Kind() == verible::SymbolKind::kNode) {
              const auto& modport_items = verible::SymbolCastToNode(*item[1]);
              for (size_t j = 0; j < modport_items.size(); j++) {
                if (modport_items[j] && modport_items[j]->Kind() == verible::SymbolKind::kNode) {
                  const auto& modport_item = verible::SymbolCastToNode(*modport_items[j]);
                  // kModportItem has identifier at child[0]
                  if (modport_item.size() > 0 && modport_item[0] &&
                      modport_item[0]->Kind() == verible::SymbolKind::kLeaf) {
                    const auto& name_leaf = verible::SymbolCastToLeaf(*modport_item[0]);
                    modport_names.push_back(std::string(name_leaf.get().text()));
                  }
                }
              }
            }
          } else if (item_tag == NodeEnum::kClockingDeclaration) {
            has_clocking_blocks = true;
          }
        }
      }
    }
    
    interface_info["signal_count"] = signal_count;
    interface_info["modport_count"] = modport_count;
    interface_info["modport_names"] = modport_names;
    interface_info["has_clocking_blocks"] = has_clocking_blocks;
    
    if (!value_->contains("metadata")) {
      (*value_)["metadata"] = json::object();
    }
    (*value_)["metadata"]["interface_info"] = interface_info;
  } else if (tag == NodeEnum::kDataDeclaration) {
    AddTypeResolutionMetadata(*value_, node, typedef_table_, context_.base);  // Phase A: Type resolution
    
    // Phase B: Cross-reference metadata for variable declarations
    auto reg_var_matches = verible::SearchSyntaxTree(node, NodekRegisterVariable());
    if (!reg_var_matches.empty()) {
      const auto* reg_node = reg_var_matches[0].match;
      if (reg_node && reg_node->Kind() == verible::SymbolKind::kNode) {
        const auto& reg_var_node = verible::SymbolCastToNode(*reg_node);
        if (reg_var_node.size() > 0 && reg_var_node[0]) {
          const auto* name_symbol = reg_var_node[0].get();
          if (name_symbol && name_symbol->Kind() == verible::SymbolKind::kLeaf) {
            const auto& name_leaf = verible::SymbolCastToLeaf(*name_symbol);
            std::string symbol_name(name_leaf.get().text());
            AddCrossReferenceMetadata(*value_, *name_symbol, symbol_table_, context_.base, symbol_name);
          }
        }
      }
    }
  } else if (tag == NodeEnum::kPortDeclaration) {
    // Phase B: Cross-reference metadata for port declarations
    // Extract port name from child 3 (kUnqualifiedId)
    if (node.size() > 3 && node[3]) {
      const auto* id_node = node[3].get();
      if (id_node && id_node->Kind() == verible::SymbolKind::kNode) {
        const auto& unqual_id_node = verible::SymbolCastToNode(*id_node);
        if (unqual_id_node.MatchesTag(NodeEnum::kUnqualifiedId) && unqual_id_node.size() > 0 && unqual_id_node[0]) {
          const auto* name_symbol = unqual_id_node[0].get();
          if (name_symbol && name_symbol->Kind() == verible::SymbolKind::kLeaf) {
            const auto& name_leaf = verible::SymbolCastToLeaf(*name_symbol);
            std::string symbol_name(name_leaf.get().text());
            AddCrossReferenceMetadata(*value_, *name_symbol, symbol_table_, context_.base, symbol_name);
          }
        }
      }
    }
  } else if (tag == NodeEnum::kParamDeclaration) {
    // Phase B: Cross-reference metadata for parameter declarations
    // Extract from kParamType (child 1) -> name (child 2)
    if (node.size() > 1 && node[1]) {
      const auto* param_type = node[1].get();
      if (param_type && param_type->Kind() == verible::SymbolKind::kNode) {
        const auto& param_type_node = verible::SymbolCastToNode(*param_type);
        if (param_type_node.size() > 2 && param_type_node[2]) {
          const auto* name_node = param_type_node[2].get();
          const verible::Symbol* name_symbol = nullptr;
          
          if (name_node->Kind() == verible::SymbolKind::kLeaf) {
            // Direct Leaf (e.g., parameter int WIDTH = 8)
            name_symbol = name_node;
          } else if (name_node->Kind() == verible::SymbolKind::kNode) {
            // kUnqualifiedId (e.g., parameter WIDTH = 8)
            const auto& unqual_node = verible::SymbolCastToNode(*name_node);
            if (unqual_node.MatchesTag(NodeEnum::kUnqualifiedId) && unqual_node.size() > 0 && unqual_node[0]) {
              name_symbol = unqual_node[0].get();
            }
          }
          
          if (name_symbol && name_symbol->Kind() == verible::SymbolKind::kLeaf) {
            const auto& name_leaf = verible::SymbolCastToLeaf(*name_symbol);
            std::string symbol_name(name_leaf.get().text());
            AddCrossReferenceMetadata(*value_, *name_symbol, symbol_table_, context_.base, symbol_name);
          }
        }
      }
    }
  } else if (tag == NodeEnum::kHierarchyExtension) {
    // Phase B: Cross-reference metadata for hierarchical extension nodes
    // Reconstruct full path by looking backward in source for the base identifier
    std::string_view hier_text = verible::StringSpanOfSymbol(node);
    
    // hier_text is like ".internal_signal"
    // We need to find the identifier before the dot in the source
    if (!context_.base.empty() && !hier_text.empty()) {
      size_t hier_offset = hier_text.data() - context_.base.data();
      
      // Search backward to find the identifier before the dot
      std::string base_identifier;
      if (hier_offset > 0) {
        size_t scan_pos = hier_offset - 1;
        // Skip whitespace
        while (scan_pos > 0 && std::isspace(context_.base[scan_pos])) {
          scan_pos--;
        }
        // Extract identifier
        size_t id_end = scan_pos + 1;
        while (scan_pos > 0 && (std::isalnum(context_.base[scan_pos]) || context_.base[scan_pos] == '_')) {
          scan_pos--;
        }
        if (!std::isalnum(context_.base[scan_pos]) && context_.base[scan_pos] != '_') {
          scan_pos++;
        }
        base_identifier = std::string(context_.base.substr(scan_pos, id_end - scan_pos));
      }
      
      std::string full_path = base_identifier + std::string(hier_text);
      
      json cross_ref = json::object();
      cross_ref["ref_type"] = "hierarchical_usage";
      cross_ref["hierarchical_path"] = full_path;
      
      if (!value_->contains("metadata")) {
        (*value_)["metadata"] = json::object();
      }
      (*value_)["metadata"]["cross_ref"] = cross_ref;
    }
  } else if (tag == NodeEnum::kReference) {
    // Phase B: Cross-reference metadata for references (usages)
    std::string_view ref_text = verible::StringSpanOfSymbol(node);
    std::string symbol_name(ref_text);
    
    // Check if this is a hierarchical reference (contains kHierarchyExtension)
    bool has_hierarchy = false;
    for (const auto& child : node.children()) {
      if (child && child->Kind() == verible::SymbolKind::kNode) {
        const auto& child_node = verible::SymbolCastToNode(*child);
        if (child_node.MatchesTag(NodeEnum::kHierarchyExtension)) {
          has_hierarchy = true;
          break;
        }
      }
    }
    
    if (has_hierarchy) {
      // This is a hierarchical reference (e.g., module.signal)
      json cross_ref = json::object();
      cross_ref["ref_type"] = "hierarchical_usage";
      cross_ref["hierarchical_path"] = std::string(ref_text);
      
      if (!value_->contains("metadata")) {
        (*value_)["metadata"] = json::object();
      }
      (*value_)["metadata"]["cross_ref"] = cross_ref;
    } else {
      // Regular reference
      // Extract just the identifier (remove array indices, field access, etc.)
      size_t bracket_pos = symbol_name.find('[');
      if (bracket_pos != std::string::npos) {
        symbol_name = symbol_name.substr(0, bracket_pos);
      }
      size_t dot_pos = symbol_name.find('.');
      if (dot_pos != std::string::npos) {
        symbol_name = symbol_name.substr(0, dot_pos);
      }
      
      AddCrossReferenceMetadata(*value_, node, symbol_table_, context_.base, symbol_name);
    }
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
  // Build typedef table for type resolution (Phase A)
  auto typedef_table = BuildTypedefTable(root, base);
  
  // Build symbol table for cross-reference tracking (Phase B)
  auto symbol_table = BuildSymbolTable(root, base);
  
  VerilogTreeToJsonConverter converter(base, typedef_table, symbol_table);
  root.Accept(&converter);
  return converter.TakeJsonValue();
}

}  // namespace verilog
