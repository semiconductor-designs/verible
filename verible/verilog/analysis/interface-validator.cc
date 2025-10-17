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

bool InterfaceValidator::ValidateModportUsage(
    std::string_view interface_name,
    std::string_view modport_name,
    std::string_view module_name) {
  // TODO: Implement modport usage validation
  // 1. Find the interface
  // 2. Find the modport
  // 3. Check if modport is used correctly in the module
  
  return true;
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
  
  // TODO: Extract interface details
  // 1. Extract signals
  info.signals = ExtractSignals(node);
  
  // 2. Extract modports
  info.modports = ExtractModports(node);
  
  // 3. Set syntax origin
  info.node = &node;
  info.syntax_origin = node.Value().syntax_origin;
  
  return info;
}

std::vector<ModportInfo> InterfaceValidator::ExtractModports(
    const SymbolTableNode& node) {
  std::vector<ModportInfo> modports;
  
  // TODO: Traverse node children to find modport declarations
  // For each modport:
  // 1. Extract modport name
  // 2. Extract signal directions
  // 3. Create ModportInfo and add to vector
  
  return modports;
}

std::vector<InterfaceSignal> InterfaceValidator::ExtractSignals(
    const SymbolTableNode& node) {
  std::vector<InterfaceSignal> signals;
  
  // TODO: Traverse node children to find signal declarations
  // For each signal:
  // 1. Extract signal name
  // 2. Extract signal type
  // 3. Extract width (if applicable)
  // 4. Create InterfaceSignal and add to vector
  
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
  
  // TODO: Check if this node is an interface definition
  // If it is:
  // 1. Extract interface name
  // 2. Extract interface definition
  // 3. Store in interfaces_ map
  
  // Recurse into children
  for (const auto& [name, child] : node) {
    TraverseForInterfaces(child);
  }
}

void InterfaceValidator::TraverseForConnections(
    const SymbolTableNode& node,
    std::string_view current_module) {
  const SymbolInfo& info = node.Value();
  
  // Track current module context
  std::string module_context(current_module);
  
  // TODO: Check if this node is a module definition
  // If it is, update module_context
  
  // TODO: Check if this node is an interface port or instance
  // If it is:
  // 1. Extract connection details
  // 2. Create InterfaceConnection
  // 3. Add to connections_ vector
  
  // Recurse into children with current module context
  for (const auto& [name, child] : node) {
    TraverseForConnections(child, module_context);
  }
}

}  // namespace analysis
}  // namespace verilog

