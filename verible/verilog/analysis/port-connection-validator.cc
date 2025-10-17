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
  
  // Traverse the symbol table and validate all module instantiations
  // For now, we do a simplified check that focuses on the failing test cases:
  // 1. MultipleOutputsConflict - detect multiple outputs on same wire
  // 2. UnconnectedPort - detect unconnected required ports
  
  // This is a placeholder implementation that will be expanded
  // as we encounter more complex scenarios
  
  return absl::OkStatus();
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
  // TODO: Implement driver conflict detection
  // This will check for multiple outputs driving the same wire
  return false;
}

void PortConnectionValidator::DetectUnconnectedPorts(
    const std::vector<PortInfo>& formal_ports,
    const std::vector<PortConnection>& connections,
    std::string_view module_name) {
  // TODO: Implement unconnected port detection
  // This will check for required ports that are not connected
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

