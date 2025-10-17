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

#include "verible/verilog/analysis/interface-validator.h"

#include <string>
#include <string_view>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "verible/common/analysis/syntax-tree-search.h"
#include "verible/common/text/concrete-syntax-leaf.h"
#include "verible/common/text/tree-utils.h"
#include "verible/verilog/CST/module.h"
#include "verible/verilog/CST/verilog-matchers.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/analysis/symbol-table.h"

namespace verilog {
namespace analysis {

InterfaceValidator::InterfaceValidator(const SymbolTable* symbol_table)
    : symbol_table_(symbol_table) {}

absl::Status InterfaceValidator::ValidateAllInterfaces() {
  // Clear previous diagnostics
  ClearDiagnostics();
  
  if (!symbol_table_) {
    return absl::InvalidArgumentError("Symbol table is null");
  }
  
  // Extract all interface definitions
  ExtractInterfaces();
  
  // Extract all interface connections
  ExtractConnections();
  
  // Validate each connection
  for (const auto& connection : connections_) {
    ValidateInterfaceConnection(connection);
  }
  
  return errors_.empty() ? absl::OkStatus() : 
         absl::FailedPreconditionError("Interface validation failed");
}

absl::Status InterfaceValidator::ValidateInterfaceConnection(
    const InterfaceConnection& connection) {
  // TODO: Implement interface connection validation
  // 1. Check if interface type exists
  // 2. Check if modport exists (if specified)
  // 3. Validate signal compatibility
  // 4. Check direction compatibility
  
  return absl::OkStatus();
}

void InterfaceValidator::ExtractInterfaces() {
  // TODO: Traverse symbol table to find all interface definitions
  // For each interface found:
  // 1. Extract interface name
  // 2. Extract signals
  // 3. Extract modports
  // 4. Store in interfaces_ map
  
  if (symbol_table_) {
    TraverseForInterfaces(symbol_table_->Root());
  }
}

InterfaceInfo InterfaceValidator::ExtractInterfaceDefinition(
    const SymbolTableNode& node,
    std::string_view interface_name) {
  InterfaceInfo info(interface_name);
  
  // Extract interface details from symbol table
  info.node = &node;
  const SymbolInfo& sym_info = node.Value();
  info.syntax_origin = sym_info.syntax_origin;
  
  // Extract signals from symbol table children
  info.signals = ExtractSignals(node);
  
  // Extract modports from symbol table children  
  info.modports = ExtractModports(node);
  
  // If we have CST syntax origin, we could extract more details
  // For now, rely on symbol table structure
  
  return info;
}

std::vector<ModportInfo> InterfaceValidator::ExtractModports(
    const SymbolTableNode& node) {
  std::vector<ModportInfo> modports;
  
  // Get the CST syntax origin for this interface
  const SymbolInfo& info = node.Value();
  if (!info.syntax_origin) {
    return modports;  // No CST available
  }
  
  // Search for modport declarations in the CST
  auto modport_matches = verible::SearchSyntaxTree(
      *info.syntax_origin, 
      NodekModportDeclaration());
  
  for (const auto& match : modport_matches) {
    if (!match.match) continue;
    
    // kModportDeclaration structure: position 1 contains a node with the name
    // Get the node at position 1 first
    const verible::SyntaxTreeNode* modport_item = 
        verible::GetSubtreeAsNode(*match.match, NodeEnum::kModportDeclaration, 1);
    
    if (modport_item && !modport_item->empty()) {
      // The name is typically the first child (position 0) of that node
      const verible::Symbol* first_child = (*modport_item)[0].get();
      if (first_child && first_child->Kind() == verible::SymbolKind::kLeaf) {
        const auto* name_leaf = verible::down_cast<const verible::SyntaxTreeLeaf*>(first_child);
        ModportInfo modport_info(name_leaf->get().text());
        modport_info.syntax_origin = match.match;
        
        // Extract signal directions from modport ports
        // Look for kModportSimplePortsDeclaration within this modport
        auto port_decls = verible::SearchSyntaxTree(
            *match.match,
            NodekModportSimplePortsDeclaration());
        
        for (const auto& port_decl : port_decls) {
          if (!port_decl.match) continue;
          
          // Extract direction (input/output/inout at position 0)
          const verible::SyntaxTreeLeaf* dir_leaf = 
              verible::GetSubtreeAsLeaf(*port_decl.match, 
                                       NodeEnum::kModportSimplePortsDeclaration, 0);
          
          ModportDirection direction = ModportDirection::kUnknown;
          if (dir_leaf) {
            std::string_view dir_text = dir_leaf->get().text();
            if (dir_text == "input") direction = ModportDirection::kInput;
            else if (dir_text == "output") direction = ModportDirection::kOutput;
            else if (dir_text == "inout") direction = ModportDirection::kInout;
            else if (dir_text == "ref") direction = ModportDirection::kRef;
          }
          
          // Extract signal names at position 1 (kModportPortsDeclaration)
          const verible::SyntaxTreeNode* signals_node = 
              verible::GetSubtreeAsNode(*port_decl.match,
                                       NodeEnum::kModportSimplePortsDeclaration, 1);
          
          if (signals_node) {
            // Search for signal identifiers within
            auto signal_ids = verible::SearchSyntaxTree(*signals_node, NodekUnqualifiedId());
            for (const auto& sig : signal_ids) {
              if (sig.match && sig.match->Kind() == verible::SymbolKind::kLeaf) {
                const auto* sig_leaf = verible::down_cast<const verible::SyntaxTreeLeaf*>(sig.match);
                modport_info.AddSignal(sig_leaf->get().text(), direction);
              }
            }
          }
        }
        
        modports.push_back(modport_info);
      }
    }
  }
  
  return modports;
}

std::vector<InterfaceSignal> InterfaceValidator::ExtractSignals(
    const SymbolTableNode& node) {
  std::vector<InterfaceSignal> signals;
  
  // Traverse node children to find signal declarations
  for (const auto& [child_name, child_node] : node) {
    const SymbolInfo& child_info = child_node.Value();
    
    // Look for variables and nets (but not modports, not modules, not other interfaces)
    if (child_info.metatype == SymbolMetaType::kDataNetVariableInstance &&
        child_info.declared_type.user_defined_type == nullptr) {  // Not a module/interface instance
      
      // Use "logic" as default type for now
      // TODO: Extract actual type from syntax tree
      InterfaceSignal signal(child_name, "logic");
      signal.syntax_origin = child_info.syntax_origin;
      
      signals.push_back(signal);
    }
  }
  
  return signals;
}

void InterfaceValidator::ExtractConnections() {
  // TODO: Traverse symbol table to find all interface connections
  // For each module that uses interfaces:
  // 1. Find interface port declarations
  // 2. Find interface instances
  // 3. Create InterfaceConnection for each usage
  
  if (symbol_table_) {
    TraverseForConnections(symbol_table_->Root(), "");
  }
}

bool InterfaceValidator::ModportExists(
    const InterfaceInfo& interface_info,
    std::string_view modport_name) const {
  return interface_info.FindModport(modport_name) != nullptr;
}

bool InterfaceValidator::CheckSignalCompatibility(
    const InterfaceInfo& interface_info,
    std::string_view modport_name,
    std::string_view usage_context) {
  // TODO: Implement signal compatibility checking
  // 1. Get the modport
  // 2. Check if signals are used according to their directions
  // 3. Verify read/write operations match input/output directions
  
  return true;
}

ModportDirection InterfaceValidator::ParseModportDirection(
    std::string_view direction_str) {
  if (direction_str == "input") {
    return ModportDirection::kInput;
  } else if (direction_str == "output") {
    return ModportDirection::kOutput;
  } else if (direction_str == "inout") {
    return ModportDirection::kInout;
  } else if (direction_str == "ref") {
    return ModportDirection::kRef;
  }
  return ModportDirection::kUnknown;
}

void InterfaceValidator::AddError(std::string_view message) {
  errors_.push_back(std::string(message));
}

void InterfaceValidator::AddWarning(std::string_view message) {
  warnings_.push_back(std::string(message));
}

void InterfaceValidator::TraverseForInterfaces(const SymbolTableNode& node) {
  const SymbolInfo& info = node.Value();
  
  // Check if this node is an interface definition
  if (info.metatype == SymbolMetaType::kInterface) {
    const auto* key = node.Key();
    if (key && !key->empty()) {
      std::string interface_name(*key);
      
      // Extract the interface definition and store directly
      interfaces_[interface_name] = ExtractInterfaceDefinition(node, interface_name);
    }
  }
  
  // Recurse into children
  for (const auto& [name, child] : node) {
    TraverseForInterfaces(child);
  }
}

const InterfaceInfo* InterfaceValidator::FindInterfaceDefinition(
    std::string_view interface_name) const {
  auto it = interfaces_.find(std::string(interface_name));
  if (it != interfaces_.end()) {
    return &it->second;
  }
  return nullptr;
}

bool InterfaceValidator::ValidateModportUsage(
    std::string_view interface_name,
    std::string_view modport_name,
    std::string_view module_name) {
  
  // Find the interface definition
  const InterfaceInfo* intf_info = FindInterfaceDefinition(interface_name);
  
  if (!intf_info) {
    AddError(absl::StrCat("Interface '", interface_name, "' not found in module '", 
                          module_name, "'"));
    return false;
  }
  
  // Check if the modport exists
  if (!ModportExists(*intf_info, modport_name)) {
    AddError(absl::StrCat("Modport '", modport_name, 
                          "' not found in interface '", interface_name, 
                          "' (used in module '", module_name, "')"));
    return false;
  }
  
  // Modport exists - validation successful
  return true;
}

void InterfaceValidator::TraverseForConnections(
    const SymbolTableNode& node,
    std::string_view current_module) {
  const SymbolInfo& info = node.Value();
  
  // Track current module context
  std::string module_context(current_module);
  
  // Update module context if this is a module definition
  if (info.metatype == SymbolMetaType::kModule) {
    module_context = std::string(*node.Key());
  }
  
  // Check if this is a port with an interface type
  if (info.is_port_identifier && 
      info.declared_type.user_defined_type != nullptr) {
    
    // Get the type identifier
    const auto& type_ref = info.declared_type.user_defined_type->Value();
    if (type_ref.identifier.empty()) {
      return;  // Skip if no identifier
    }
    
    // Parse the type to see if it has a modport specification
    // Format: "interface_name.modport_name"
    std::string_view type_name = type_ref.identifier;
    size_t dot_pos = type_name.find('.');
    
    if (dot_pos != std::string_view::npos) {
      // Has modport specification
      std::string_view intf_name = type_name.substr(0, dot_pos);
      std::string_view modport_name = type_name.substr(dot_pos + 1);
      
      // Validate the modport usage
      ValidateModportUsage(intf_name, modport_name, module_context);
    }
  }
  
  // Recurse into children with current module context
  for (const auto& [name, child] : node) {
    TraverseForConnections(child, module_context);
  }
}

}  // namespace analysis
}  // namespace verilog

