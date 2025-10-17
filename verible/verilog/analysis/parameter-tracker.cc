// Copyright 2017-2025 The Verible Authors.
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

#include "verible/verilog/analysis/parameter-tracker.h"

#include <string>
#include <string_view>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "verible/common/text/concrete-syntax-leaf.h"
#include "verible/common/text/concrete-syntax-tree.h"
#include "verible/common/text/symbol.h"
#include "verible/common/text/token-info.h"
#include "verible/common/text/tree-utils.h"
#include "verible/verilog/CST/parameters.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/parser/verilog-token-enum.h"

namespace verilog {
namespace analysis {

absl::Status ParameterTracker::TrackAllParameters() {
  // Clear previous state
  ClearDiagnostics();
  parameters_.clear();
  
  if (!symbol_table_) {
    return absl::InvalidArgumentError("Symbol table is null");
  }
  
  // Extract all parameter definitions
  ExtractParameters();
  
  // Extract all parameter overrides
  ExtractOverrides();
  
  return absl::OkStatus();
}

absl::Status ParameterTracker::ValidateParameters() {
  // Validation happens during extraction and override tracking
  // Return error if any errors were found
  return errors_.empty() ? absl::OkStatus() : 
         absl::InvalidArgumentError(absl::StrCat(errors_.size(), " parameter error(s) found"));
}

void ParameterTracker::ExtractParameters() {
  if (!symbol_table_) return;
  
  // Traverse modules in symbol table to get module context
  TraverseForModules(symbol_table_->Root());
}

void ParameterTracker::TraverseForModules(const SymbolTableNode& node) {
  const SymbolInfo& info = node.Value();
  
  // If this is a module, extract its parameters from CST
  if (info.metatype == SymbolMetaType::kModule && info.syntax_origin) {
    const auto* key = node.Key();
    if (key && !key->empty()) {
      std::string module_name(*key);
      ExtractParametersFromModule(*info.syntax_origin, module_name);
    }
  }
  
  // Recurse into children
  for (const auto& [name, child] : node) {
    TraverseForModules(child);
  }
}

void ParameterTracker::ExtractParametersFromModule(
    const verible::Symbol& module_symbol,
    std::string_view module_name) {
  
  // Find all parameter declarations in this module
  auto param_decls = FindAllParamDeclarations(module_symbol);
  
  for (const auto& match : param_decls) {
    if (!match.match) continue;
    
    // Get parameter name
    const verible::TokenInfo* name_token = GetParameterNameToken(*match.match);
    if (!name_token) continue;
    
    std::string param_name(name_token->text());
    std::string qualified_name = absl::StrCat(module_name, ".", param_name);
    
    // Extract parameter details
    ParameterInfo info(param_name);
    info.syntax_origin = match.match;
    
    // Determine if localparam
    verilog_tokentype keyword = GetParamKeyword(*match.match);
    info.is_localparam = (keyword == TK_localparam);
    
    // Extract default value
    const verible::Symbol* expr = GetParamAssignExpression(*match.match);
    if (expr) {
      info.default_value = verible::StringSpanOfSymbol(*expr);
    }
    
    // Extract type information
    const verible::Symbol* type_info = GetParamTypeInfoSymbol(*match.match);
    if (type_info && !IsTypeInfoEmpty(*type_info)) {
      info.type = verible::StringSpanOfSymbol(*type_info);
    }
    
    // Store
    parameters_[qualified_name] = info;
  }
}

void ParameterTracker::TraverseForParameters(const SymbolTableNode& node,
                                            std::string_view module_context) {
  // DEPRECATED: Parameters are not stored in symbol table as separate nodes
  // Use ExtractParametersFromModule instead
}

ParameterInfo ParameterTracker::ExtractParameterDefinition(
    const SymbolTableNode& node,
    std::string_view param_name,
    std::string_view module_context) {
  ParameterInfo info(param_name);
  
  const SymbolInfo& sym_info = node.Value();
  info.node = &node;
  info.syntax_origin = sym_info.syntax_origin;
  
  // Extract from CST if available
  if (sym_info.syntax_origin) {
    // Determine if this is a localparam by checking the keyword
    verilog_tokentype keyword = GetParamKeyword(*sym_info.syntax_origin);
    info.is_localparam = (keyword == TK_localparam);
    
    // Extract default value from CST
    const verible::Symbol* expr = GetParamAssignExpression(*sym_info.syntax_origin);
    if (expr) {
      info.default_value = verible::StringSpanOfSymbol(*expr);
    }
    
    // Extract type information
    const verible::Symbol* type_info = GetParamTypeInfoSymbol(*sym_info.syntax_origin);
    if (type_info && !IsTypeInfoEmpty(*type_info)) {
      info.type = verible::StringSpanOfSymbol(*type_info);
    }
  }
  
  // Fallback to symbol table if CST extraction didn't work
  if (info.type.empty()) {
    info.type = ParseParameterType(node);
  }
  
  return info;
}

void ParameterTracker::ExtractOverrides() {
  if (symbol_table_) {
    TraverseForOverrides(symbol_table_->Root(), "");
  }
}

void ParameterTracker::TraverseForOverrides(const SymbolTableNode& node,
                                           std::string_view module_context) {
  const SymbolInfo& info = node.Value();
  
  // Update module context
  std::string current_module(module_context);
  if (info.metatype == SymbolMetaType::kModule) {
    current_module = std::string(*node.Key());
  }
  
  // Check if this is a module instance with parameter overrides
  if (info.metatype == SymbolMetaType::kDataNetVariableInstance &&
      info.declared_type.user_defined_type != nullptr) {
    // TODO: Extract parameter overrides from CST
    // This requires parsing the module instantiation syntax
  }
  
  // Recurse into children
  for (const auto& [name, child] : node) {
    TraverseForOverrides(child, current_module);
  }
}

bool ParameterTracker::ValidateParameterOverride(
    std::string_view module_name,
    std::string_view param_name,
    std::string_view instance_name,
    std::string_view new_value) {
  
  // Find the parameter definition
  const ParameterInfo* param = FindParameter(module_name, param_name);
  
  if (!param) {
    AddError(absl::StrCat("Parameter '", param_name, "' not found in module '", 
                          module_name, "'"));
    return false;
  }
  
  // Check if parameter can be overridden
  if (!param->CanBeOverridden()) {
    AddError(absl::StrCat("Cannot override localparam '", param_name, 
                          "' in module '", module_name, "' (instance: ", 
                          instance_name, ")"));
    return false;
  }
  
  // TODO: Add type checking if type information is available
  
  return true;
}

const ParameterInfo* ParameterTracker::FindParameter(
    std::string_view module_name,
    std::string_view param_name) const {
  std::string qualified_name = absl::StrCat(module_name, ".", param_name);
  auto it = parameters_.find(qualified_name);
  if (it != parameters_.end()) {
    return &it->second;
  }
  return nullptr;
}

std::string ParameterTracker::ParseParameterType(
    const SymbolTableNode& node) const {
  const SymbolInfo& info = node.Value();
  
  // Try to get type from declared_type
  if (info.declared_type.user_defined_type != nullptr) {
    const auto& type_ref = info.declared_type.user_defined_type->Value();
    if (!type_ref.identifier.empty()) {
      return std::string(type_ref.identifier);
    }
  }
  
  // Default to unspecified
  return "unspecified";
}

std::string ParameterTracker::ParseParameterValue(
    const SymbolTableNode& node) const {
  // TODO: Extract default value from CST
  // For now, return empty string
  return "";
}

void ParameterTracker::AddError(std::string_view message) {
  errors_.push_back(std::string(message));
}

void ParameterTracker::AddWarning(std::string_view message) {
  warnings_.push_back(std::string(message));
}

}  // namespace analysis
}  // namespace verilog

