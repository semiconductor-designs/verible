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
#include "verible/common/text/symbol.h"
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
  // We need to:
  // 1. Find all modules
  // 2. For each module, find instances of other modules
  // 3. Extract port connections for each instance
  // 4. Validate connections (direction, type, completeness)
  // 5. Detect driver conflicts within each parent module
  
  ValidateModuleHierarchy(symbol_table_->Root());
  
  return errors_.empty() ? absl::OkStatus() : 
         absl::FailedPreconditionError("Port connection validation failed");
}

// Helper to recursively validate module hierarchy
void PortConnectionValidator::ValidateModuleHierarchy(
    const SymbolTableNode& node) {
  const SymbolInfo& info = node.Value();
  
  // If this is a module, validate its instances
  if (info.metatype == SymbolMetaType::kModule) {
    std::string_view module_name = *node.Key();
    ValidateModuleInstances(node, module_name);
  }
  
  // Recurse into children
  for (const auto& [name, child] : node) {
    ValidateModuleHierarchy(child);
  }
}

// Helper to validate all instances within a module
void PortConnectionValidator::ValidateModuleInstances(
    const SymbolTableNode& module_node,
    std::string_view module_name) {
  // Track all output connections in this module for driver conflict detection
  std::map<std::string, std::vector<std::string>> signal_to_output_instances;
  
  // Find all module instances within this module
  // Instances are represented as kDataNetVariableInstance with a user_defined_type
  for (const auto& [inst_name, inst_node] : module_node) {
    const SymbolInfo& inst_info = inst_node.Value();
    
    // Check if this is a module instance
    if (inst_info.metatype == SymbolMetaType::kDataNetVariableInstance &&
        inst_info.declared_type.user_defined_type != nullptr) {
      
      // Get the module type being instantiated
      const ReferenceComponentNode* type_ref = inst_info.declared_type.user_defined_type;
      if (type_ref && type_ref->Children().size() > 0) {
        std::string module_type(type_ref->Children().front().Value().identifier);
        
        // Find the module definition in the symbol table
        const SymbolTableNode* module_def = FindModuleDefinition(module_type);
        if (module_def) {
          // Extract ports from the module definition
          std::vector<PortInfo> formal_ports = ExtractPorts(*module_def);
          
          // Extract connections from this instance (stub for now)
          std::vector<PortConnection> connections;  // TODO: Extract from CST
          
          // For driver conflict detection, track output ports
          for (const auto& port : formal_ports) {
            if (port.direction == PortDirection::kOutput) {
              // In a real implementation, we'd get the actual signal name from CST
              // For now, we'll use a simplified approach
              std::string signal_name = std::string(inst_name) + "_signal";
              signal_to_output_instances[signal_name].push_back(std::string(inst_name));
            }
          }
          
          // Check for unconnected ports
          DetectUnconnectedPorts(formal_ports, connections, module_type);
        }
      }
    }
  }
  
  // Check for driver conflicts (multiple outputs on same wire)
  for (const auto& [signal, instances] : signal_to_output_instances) {
    if (instances.size() > 1) {
      AddError(absl::StrCat("Multiple outputs driving signal '", signal,
                            "' in module '", module_name, "'"));
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
  if (*node.Key() == module_name && 
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
  
  // TODO: Implement connection extraction from module instance
  // This will traverse the CST to find port connections
  
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

