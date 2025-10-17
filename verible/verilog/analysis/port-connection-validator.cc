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

#include "verible/verilog/analysis/port-connection-validator.h"

#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "verible/common/analysis/syntax-tree-search.h"
#include "verible/common/text/concrete-syntax-leaf.h"
#include "verible/common/text/concrete-syntax-tree.h"
#include "verible/common/text/symbol.h"
#include "verible/common/text/tree-utils.h"
#include "verible/verilog/CST/port.h"
#include "verible/verilog/analysis/symbol-table.h"

namespace verilog {
namespace analysis {

PortConnectionValidator::PortConnectionValidator(const SymbolTable* symbol_table)
    : symbol_table_(symbol_table) {}

absl::Status PortConnectionValidator::ValidateAllConnections() {
  // Clear previous diagnostics
  ClearDiagnostics();
  
  if (!symbol_table_) {
    return absl::InvalidArgumentError("Symbol table is null");
  }
  
  // Traverse the symbol table to find and validate all module instances
  ValidateModuleHierarchy(symbol_table_->Root());
  
  return errors_.empty() ? absl::OkStatus() : 
         absl::FailedPreconditionError("Port connection validation failed");
}

// Helper to recursively validate module hierarchy
void PortConnectionValidator::ValidateModuleHierarchy(
    const SymbolTableNode& node) {
  ValidateModuleHierarchyWithContext(node, "");
}

void PortConnectionValidator::ValidateModuleHierarchyWithContext(
    const SymbolTableNode& node, const std::string& current_module) {
  const SymbolInfo& info = node.Value();
  
  // Track the current module context (like multi-file-resolver does)
  std::string module_context = current_module;
  
  // If this is a module definition, update the context and collect all instances
  if (info.metatype == SymbolMetaType::kModule) {
    const auto* key = node.Key();
    if (key && !key->empty()) {
      module_context = std::string(*key);
      
      // Collect all instances in this module to check for driver conflicts
      std::map<std::string, std::vector<std::string>> signal_drivers;
      CollectModuleInstances(node, module_context, signal_drivers);
      
      // Check for driver conflicts across all instances
      for (const auto& [signal, drivers] : signal_drivers) {
        if (drivers.size() > 1) {
          AddError(absl::StrCat("Multiple outputs driving signal '", signal,
                                "' in module '", module_context, "' (",
                                drivers.size(), " drivers: ",
                                absl::StrJoin(drivers, ", "), ")"));
        }
      }
    }
  }
  
  // Recurse into all children with the current module context
  for (const auto& [name, child] : node) {
    ValidateModuleHierarchyWithContext(child, module_context);
  }
}

// Helper to collect all instances in a module and track drivers
void PortConnectionValidator::CollectModuleInstances(
    const SymbolTableNode& module_node,
    std::string_view module_name,
    std::map<std::string, std::vector<std::string>>& signal_drivers) {
  
  // Iterate through direct children only (not recursive - modules nest)
  for (const auto& [child_name, child_node] : module_node) {
    const SymbolInfo& child_info = child_node.Value();
    
    // Check if this child is a module instance
    if (child_info.metatype == SymbolMetaType::kDataNetVariableInstance &&
        child_info.declared_type.user_defined_type != nullptr) {
      
      // Validate this single instance and track its drivers
      ValidateSingleInstanceAndTrackDrivers(child_node, child_name, module_name, signal_drivers);
    }
  }
}

// Helper to validate a single module instance
void PortConnectionValidator::ValidateSingleInstance(
    const SymbolTableNode& instance_node,
    std::string_view instance_name,
    std::string_view parent_module) {
  std::map<std::string, std::vector<std::string>> dummy_drivers;
  ValidateSingleInstanceAndTrackDrivers(instance_node, instance_name, parent_module, dummy_drivers);
}

// Helper to validate a single module instance and track drivers
void PortConnectionValidator::ValidateSingleInstanceAndTrackDrivers(
    const SymbolTableNode& instance_node,
    std::string_view instance_name,
    std::string_view parent_module,
    std::map<std::string, std::vector<std::string>>& signal_drivers) {
  
  const SymbolInfo& inst_info = instance_node.Value();
  
  // Get the module type name
  const auto& ref_comp = inst_info.declared_type.user_defined_type->Value();
  std::string_view module_type = ref_comp.identifier;
  
  if (module_type.empty()) {
    return;  // No valid module type
  }
  
  // Find the module definition
  const SymbolTableNode* module_def = FindModuleDefinition(module_type);
  if (!module_def) {
    AddWarning(absl::StrCat("Module definition '", module_type, "' not found for instance '", instance_name, "'"));
    return;
  }
  
  // Extract ports from the module definition
  std::vector<PortInfo> formal_ports = ExtractPorts(*module_def);
  
  // Extract connections from this instance
  std::vector<PortConnection> connections = ExtractConnections(instance_node);
  
  // Link connections to formal ports and track output drivers
  for (auto& conn : connections) {
    for (const auto& port : formal_ports) {
      if (port.name == conn.formal_name) {
        conn.formal_port = &port;
        
        // If this is an output port, track it as driving the actual signal
        if (port.direction == PortDirection::kOutput && !conn.actual_expression.empty()) {
          signal_drivers[std::string(conn.actual_expression)].push_back(std::string(instance_name));
        }
        break;
      }
    }
  }
  
  // Detect unconnected ports (driver conflicts checked at module level)
  DetectUnconnectedPorts(formal_ports, connections, module_type);
}

// Helper to validate all instances within a module
void PortConnectionValidator::ValidateModuleInstances(
    const SymbolTableNode& module_node,
    std::string_view module_name) {
  // Track all output connections in this module for driver conflict detection
  std::map<std::string, std::vector<std::string>> signal_to_output_instances;
  
  // DEBUG: Track if we found any instances
  int instance_count = 0;
  
  // Find all module instances within this module
  // Instances are represented as kDataNetVariableInstance with a user_defined_type
  for (const auto& [inst_name, inst_node] : module_node) {
    const SymbolInfo& inst_info = inst_node.Value();
    
    // Check if this is a module instance
    if (inst_info.metatype == SymbolMetaType::kDataNetVariableInstance) {
      // Module instances have a user_defined_type
      if (inst_info.declared_type.user_defined_type != nullptr) {
        instance_count++;  // DEBUG
        
        // Get the module type name from the reference (matching multi-file-resolver pattern)
        const auto& ref_comp = inst_info.declared_type.user_defined_type->Value();
        std::string_view module_type = ref_comp.identifier;
        
        if (module_type.empty()) {
          continue;  // No valid module type
        }
        
        // Find the module definition in the symbol table
        const SymbolTableNode* module_def = FindModuleDefinition(module_type);
        if (module_def) {
          // Extract ports from the module definition
          std::vector<PortInfo> formal_ports = ExtractPorts(*module_def);
          
          // Extract connections from this instance
          std::vector<PortConnection> connections = ExtractConnections(inst_node);
          
          // DEBUG: Always log what we found
          AddWarning(absl::StrCat("DEBUG: Instance '", inst_name, 
                                  "' of '", module_type,
                                  "': ", formal_ports.size(), " ports, ",
                                  connections.size(), " connections"));
          
          // Link connections to formal ports
          for (auto& conn : connections) {
            for (const auto& port : formal_ports) {
              if (port.name == conn.formal_name) {
                conn.formal_port = &port;
                break;
              }
            }
          }
          
          // For driver conflict detection, track output port connections
          for (const auto& conn : connections) {
            if (conn.formal_port && 
                conn.formal_port->direction == PortDirection::kOutput &&
                !conn.actual_expression.empty()) {
              // Track which signal this output is driving
              signal_to_output_instances[conn.actual_expression].push_back(
                  std::string(inst_name));
            }
          }
          
          // Check for unconnected ports
          DetectUnconnectedPorts(formal_ports, connections, module_type);
        }
      }
    }
  }
  
  // DEBUG: Report what we found
  if (instance_count == 0) {
    // No instances found - this might be expected for leaf modules
  }
  
  // Check for driver conflicts (multiple outputs on same wire)
  for (const auto& [signal, instances] : signal_to_output_instances) {
    if (instances.size() > 1) {
      AddError(absl::StrCat("Multiple outputs driving signal '", signal,
                            "' in module '", module_name, "' (",
                            instances.size(), " drivers)"));
    }
  }
}

// Helper to find a module definition by name
const SymbolTableNode* PortConnectionValidator::FindModuleDefinition(
    std::string_view module_name) const {
  // Search the symbol table for the module definition
  return FindModuleInNode(symbol_table_->Root(), module_name);
}

// Recursive helper to find module in node tree
const SymbolTableNode* PortConnectionValidator::FindModuleInNode(
    const SymbolTableNode& node, std::string_view module_name) const {
  // Check if this node is the module we're looking for
  const auto* key = node.Key();
  if (key && *key == module_name && 
      node.Value().metatype == SymbolMetaType::kModule) {
    return &node;
  }
  
  // Search children
  for (const auto& [name, child] : node) {
    if (const SymbolTableNode* found = FindModuleInNode(child, module_name)) {
      return found;
    }
  }
  
  return nullptr;
}

absl::Status PortConnectionValidator::ValidateInstance(
    std::string_view instance_name, std::string_view module_type) {
  // TODO: Implement instance validation
  return absl::OkStatus();
}

absl::Status PortConnectionValidator::ValidateConnection(
    const PortConnection& connection, std::string_view module_name) {
  // TODO: Implement connection validation
  return absl::OkStatus();
}

std::vector<PortInfo> PortConnectionValidator::ExtractPorts(
    const SymbolTableNode& module_node) {
  std::vector<PortInfo> ports;
  
  // Recursively traverse the module's children to find port declarations
  // Ports are identified by is_port_identifier flag in SymbolInfo
  for (const auto& [name, child_node] : module_node) {
    const SymbolInfo& info = child_node.Value();
    
    // Check if this is a port identifier
    if (info.is_port_identifier) {
      PortInfo port_info(name, ParsePortDirection(child_node));
      
      // Extract port direction from declared_type.direction
      if (!info.declared_type.direction.empty()) {
        std::string_view dir = info.declared_type.direction;
        if (dir == "input") {
          port_info.direction = PortDirection::kInput;
        } else if (dir == "output") {
          port_info.direction = PortDirection::kOutput;
        } else if (dir == "inout") {
          port_info.direction = PortDirection::kInout;
        } else if (dir == "ref") {
          port_info.direction = PortDirection::kRef;
        }
      }
      
      // Extract port width
      port_info.width = ParsePortWidth(child_node);
      
      // Store syntax origin
      port_info.syntax_origin = info.syntax_origin;
      
      ports.push_back(port_info);
    }
  }
  
  return ports;
}

std::vector<PortConnection> PortConnectionValidator::ExtractConnections(
    const SymbolTableNode& instance_node) {
  std::vector<PortConnection> connections;
  
  const SymbolInfo& inst_info = instance_node.Value();
  if (!inst_info.syntax_origin) {
    return connections;  // No CST node available
  }
  
  // Find all named port connections (.port_name(expression))
  auto named_ports = FindAllActualNamedPort(*inst_info.syntax_origin);
  
  for (const auto& port_match : named_ports) {
    const verible::Symbol* port_symbol = port_match.match;
    if (!port_symbol) continue;
    
    // Extract port name
    const verible::SyntaxTreeLeaf* port_name_leaf = 
        GetActualNamedPortName(*port_symbol);
    if (!port_name_leaf) continue;
    
    std::string formal_name(port_name_leaf->get().text());
    
    // Extract the actual expression (what's connected to the port)
    const verible::Symbol* paren_group = GetActualNamedPortParenGroup(*port_symbol);
    std::string actual_expr;
    
    if (paren_group) {
      // Get the text of the expression inside the parentheses
      actual_expr = verible::StringSpanOfSymbol(*paren_group);
      // Remove parentheses
      if (actual_expr.size() >= 2 && actual_expr.front() == '(' && actual_expr.back() == ')') {
        actual_expr = actual_expr.substr(1, actual_expr.size() - 2);
      }
    } else {
      // Empty connection like .port()
      actual_expr = "";
    }
    
    PortConnection conn(formal_name, actual_expr);
    conn.syntax_origin = port_symbol;
    connections.push_back(conn);
  }
  
  return connections;
}

bool PortConnectionValidator::IsDirectionCompatible(
    PortDirection formal_dir, std::string_view actual_context) {
  // TODO: Implement direction compatibility checking
  // For now, assume compatible
  return true;
}

bool PortConnectionValidator::AreTypesCompatible(
    std::string_view formal_type, std::string_view actual_type) {
  // TODO: Implement type compatibility checking
  // For now, assume compatible
  return true;
}

bool PortConnectionValidator::AreWidthsCompatible(int formal_width,
                                                   int actual_width) {
  // TODO: Implement width compatibility checking
  // For now, assume compatible
  if (formal_width == -1 || actual_width == -1) {
    return true;  // Unknown widths assumed compatible
  }
  return formal_width == actual_width;
}

bool PortConnectionValidator::DetectDriverConflicts(
    const std::vector<PortConnection>& connections) {
  // Track which signals are being driven by output ports
  std::map<std::string, int> signal_drivers;
  
  for (const auto& conn : connections) {
    if (conn.formal_port && 
        conn.formal_port->direction == PortDirection::kOutput) {
      // This is an output port connection - it drives the actual signal
      signal_drivers[conn.actual_expression]++;
    }
  }
  
  // Check for multiple drivers
  bool has_conflicts = false;
  for (const auto& [signal, count] : signal_drivers) {
    if (count > 1) {
      AddError(absl::StrCat("Multiple outputs driving signal '", signal, 
                            "' (", count, " drivers)"));
      has_conflicts = true;
    }
  }
  
  return has_conflicts;
}

void PortConnectionValidator::DetectUnconnectedPorts(
    const std::vector<PortInfo>& formal_ports,
    const std::vector<PortConnection>& connections,
    std::string_view module_name) {
  // Build set of connected port names
  std::set<std::string> connected_ports;
  for (const auto& conn : connections) {
    connected_ports.insert(conn.formal_name);
  }
  
  // Check each formal port
  for (const auto& port : formal_ports) {
    if (connected_ports.count(port.name) == 0) {
      // Port is not connected
      if (port.direction == PortDirection::kInput) {
        // Unconnected input is a warning (might have default value)
        AddWarning(absl::StrCat("Unconnected input port '", port.name, 
                                "' in module '", module_name, "'"));
      } else if (port.direction == PortDirection::kOutput) {
        // Unconnected output is also a warning (unused output)
        AddWarning(absl::StrCat("Unconnected output port '", port.name,
                                "' in module '", module_name, "'"));
      }
    }
  }
}

PortDirection PortConnectionValidator::ParsePortDirection(
    const SymbolTableNode& node) {
  // TODO: Implement port direction parsing from symbol table
  // For now, return unknown
  return PortDirection::kUnknown;
}

int PortConnectionValidator::ParsePortWidth(const SymbolTableNode& node) {
  // TODO: Implement port width parsing from symbol table
  // For now, return unknown width
  return -1;
}

void PortConnectionValidator::AddError(std::string_view message) {
  errors_.push_back(std::string(message));
}

void PortConnectionValidator::AddWarning(std::string_view message) {
  warnings_.push_back(std::string(message));
}

}  // namespace analysis
}  // namespace verilog

