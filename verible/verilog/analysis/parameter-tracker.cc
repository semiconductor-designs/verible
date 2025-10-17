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
#include "verible/common/analysis/syntax-tree-search.h"
#include "verible/common/text/concrete-syntax-leaf.h"
#include "verible/common/text/concrete-syntax-tree.h"
#include "verible/common/text/symbol.h"
#include "verible/common/text/token-info.h"
#include "verible/common/text/tree-utils.h"
#include "verible/verilog/CST/parameters.h"
#include "verible/verilog/CST/type.h"
#include "verible/verilog/CST/verilog-matchers.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
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
  
  // Update module context and extract overrides from this module's CST
  if (info.metatype == SymbolMetaType::kModule && info.syntax_origin) {
    const auto* key = node.Key();
    if (key && !key->empty()) {
      std::string module_name(*key);
      
      // Search for all kDataDeclaration nodes in this module
      // These contain both kInstantiationType (with params) and kRegisterVariable (instances)
      auto data_decls = verible::SearchSyntaxTree(*info.syntax_origin, 
                                                  NodekDataDeclaration());
      
      for (const auto& decl_match : data_decls) {
        if (!decl_match.match) continue;
        
        // Look for kInstantiationType within this declaration
        auto inst_types = verible::SearchSyntaxTree(*decl_match.match,
                                                    NodekInstantiationType());
        
        if (inst_types.empty()) continue;  // Not a module instantiation
        
        // Get the module type name and parameter list from kInstantiationType
        for (const auto& inst_type : inst_types) {
          if (!inst_type.match) continue;
          
          // Get module type
          const verible::Symbol* type_id = 
              GetTypeIdentifierFromInstantiationType(*inst_type.match);
          if (!type_id) continue;
          
          std::string module_type(verible::StringSpanOfSymbol(*type_id));
          
          // Get parameter list
          const verible::SyntaxTreeNode* param_list = 
              GetParamListFromInstantiationType(*inst_type.match);
          
          if (!param_list) continue;  // No parameter overrides
          
          // Now find all instances in this declaration
          auto instances = verible::SearchSyntaxTree(*decl_match.match,
                                                    NodekRegisterVariable());
          
          for (const auto& inst : instances) {
            if (!inst.match) continue;
            
            // Get instance name
            std::string instance_name(verible::StringSpanOfSymbol(*inst.match));
            
            // Extract parameter overrides for this instance
            // TODO: Verify instance name extraction is correct
            ExtractParameterOverridesFromList(*param_list, module_type, instance_name);
          }
        }
      }
    }
  }
  
  // Recurse into children
  for (const auto& [name, child] : node) {
    TraverseForOverrides(child, module_context);
  }
}

void ParameterTracker::ExtractParameterOverridesFromList(
    const verible::Symbol& param_list,
    std::string_view module_type,
    std::string_view instance_name) {
  
  // Find all named parameter assignments within the parameter list
  auto param_overrides = FindAllNamedParams(param_list);
  
  for (const auto& match : param_overrides) {
    if (!match.match) continue;
    
    // Get parameter name
    const verible::SyntaxTreeLeaf* param_leaf = GetNamedParamFromActualParam(*match.match);
    if (!param_leaf) continue;
    
    std::string param_name(param_leaf->get().text());
    
    // Get parameter value
    const verible::SyntaxTreeNode* value_node = GetParenGroupFromActualParam(*match.match);
    std::string param_value;
    if (value_node) {
      param_value = verible::StringSpanOfSymbol(*value_node);
    }
    
    // Validate and store the override
    ValidateParameterOverride(module_type, param_name, instance_name, param_value);
  }
}

void ParameterTracker::ExtractParameterOverrides(
    const verible::Symbol& instance_symbol,
    std::string_view module_type,
    std::string_view instance_name) {
  // DEPRECATED: This function is no longer used
  // Parameter overrides are now extracted via TraverseForOverrides
  // which searches kDataDeclaration nodes in modules
}

bool ParameterTracker::ValidateParameterOverride(
    std::string_view module_name,
    std::string_view param_name,
    std::string_view instance_name,
    std::string_view new_value) {
  
  // Find the parameter definition
  std::string qualified_name = absl::StrCat(module_name, ".", param_name);
  auto it = parameters_.find(qualified_name);
  
  if (it == parameters_.end()) {
    AddError(absl::StrCat("Parameter '", param_name, "' not found in module '", 
                          module_name, "'"));
    return false;
  }
  
  // Check if parameter can be overridden
  if (!it->second.CanBeOverridden()) {
    AddError(absl::StrCat("Cannot override localparam '", param_name, 
                          "' in module '", module_name, "' (instance: ", 
                          instance_name, ")"));
    return false;
  }
  
  // Store the override
  it->second.AddOverride(instance_name, new_value);
  
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

