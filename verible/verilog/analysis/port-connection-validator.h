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

#ifndef VERIBLE_VERILOG_ANALYSIS_PORT_CONNECTION_VALIDATOR_H_
#define VERIBLE_VERILOG_ANALYSIS_PORT_CONNECTION_VALIDATOR_H_

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "verible/common/text/symbol.h"
#include "verible/verilog/analysis/symbol-table.h"

namespace verilog {
namespace analysis {

// Port direction enumeration
enum class PortDirection {
  kInput,   // Input port
  kOutput,  // Output port
  kInout,   // Bidirectional port
  kRef,     // Reference port (SystemVerilog ref)
  kUnknown  // Unknown or unspecified direction
};

// Information about a port declaration in a module
struct PortInfo {
  std::string name;                      // Port name
  PortDirection direction;               // Port direction (input/output/inout/ref)
  std::string type_name;                 // Type name (if user-defined)
  int width;                             // Bit width (-1 for unknown/unpacked)
  bool is_packed_array;                  // True if packed array [N:0][M:0]
  bool is_unpacked_array;                // True if unpacked array [N:0] var [M:0]
  const verible::Symbol* syntax_origin;  // Pointer to CST node
  
  PortInfo(std::string_view name, PortDirection dir)
      : name(name),
        direction(dir),
        width(-1),
        is_packed_array(false),
        is_unpacked_array(false),
        syntax_origin(nullptr) {}
};

// Information about a port connection in a module instance
struct PortConnection {
  std::string formal_name;         // Port name in module definition
  std::string actual_expression;   // Expression in module instance
  const PortInfo* formal_port;     // Pointer to formal port info
  const verible::Symbol* syntax_origin;  // Pointer to CST node
  
  PortConnection(std::string_view formal, std::string_view actual)
      : formal_name(formal),
        actual_expression(actual),
        formal_port(nullptr),
        syntax_origin(nullptr) {}
};

// Validates port connections in SystemVerilog module instantiations
//
// This validator checks:
// 1. Port direction compatibility (outputs don't conflict, inputs are driven)
// 2. Port type compatibility (types match at module boundaries)
// 3. Port width compatibility (bit widths match or are compatible)
// 4. Port existence (all connections reference valid ports)
// 5. Port completeness (all required ports are connected)
//
// Example usage:
//   PortConnectionValidator validator(symbol_table);
//   absl::Status status = validator.ValidateAllConnections();
//   if (!status.ok()) {
//     for (const auto& error : validator.GetErrors()) {
//       std::cerr << error << std::endl;
//     }
//   }
class PortConnectionValidator {
 public:
  // Constructor
  // Args:
  //   symbol_table: The symbol table containing module definitions and instances
  explicit PortConnectionValidator(const SymbolTable* symbol_table);

  // Validates all port connections found in the symbol table
  // Returns:
  //   absl::Status::OK if all connections are valid, error status otherwise
  absl::Status ValidateAllConnections();

  // Validates port connections for a specific module instance
  // Args:
  //   instance_name: Name of the module instance to validate
  //   module_type: Type of module being instantiated
  // Returns:
  //   absl::Status::OK if connections are valid, error status otherwise
  absl::Status ValidateInstance(std::string_view instance_name,
                                 std::string_view module_type);

  // Validates a specific port connection
  // Args:
  //   connection: The port connection to validate
  //   module_name: Name of the module being instantiated
  // Returns:
  //   absl::Status::OK if connection is valid, error status otherwise
  absl::Status ValidateConnection(const PortConnection& connection,
                                   std::string_view module_name);

  // Gets all validation errors
  const std::vector<std::string>& GetErrors() const { return errors_; }

  // Gets all validation warnings
  const std::vector<std::string>& GetWarnings() const { return warnings_; }

  // Clears all errors and warnings
  void ClearDiagnostics() {
    errors_.clear();
    warnings_.clear();
  }

 private:
  // Extracts port information from a module definition
  // Args:
  //   module_node: The symbol table node representing the module
  // Returns:
  //   Vector of PortInfo structures
  std::vector<PortInfo> ExtractPorts(const SymbolTableNode& module_node);

  // Extracts port connections from a module instance
  // Args:
  //   instance_node: The symbol table node representing the instance
  // Returns:
  //   Vector of PortConnection structures
  std::vector<PortConnection> ExtractConnections(
      const SymbolTableNode& instance_node);

  // Validates port direction compatibility
  // Args:
  //   formal_dir: Direction of formal port (in module definition)
  //   actual_context: Context of actual connection (driving/driven)
  // Returns:
  //   true if directions are compatible, false otherwise
  bool IsDirectionCompatible(PortDirection formal_dir,
                             std::string_view actual_context);

  // Validates port type compatibility
  // Args:
  //   formal_type: Type of formal port
  //   actual_type: Type of actual connection
  // Returns:
  //   true if types are compatible, false otherwise
  bool AreTypesCompatible(std::string_view formal_type,
                          std::string_view actual_type);

  // Validates port width compatibility
  // Args:
  //   formal_width: Bit width of formal port
  //   actual_width: Bit width of actual connection
  // Returns:
  //   true if widths are compatible, false otherwise
  bool AreWidthsCompatible(int formal_width, int actual_width);

  // Detects multiple drivers on the same wire (output conflict)
  // Args:
  //   connections: All connections in the parent module
  // Returns:
  //   true if driver conflicts detected, false otherwise
  bool DetectDriverConflicts(const std::vector<PortConnection>& connections);

  // Detects unconnected required ports
  // Args:
  //   formal_ports: All ports in module definition
  //   connections: All connections in instance
  //   module_name: Name of module for error messages
  void DetectUnconnectedPorts(const std::vector<PortInfo>& formal_ports,
                               const std::vector<PortConnection>& connections,
                               std::string_view module_name);

  // Parses port direction from symbol table node
  // Args:
  //   node: The symbol table node
  // Returns:
  //   Port direction enum
  PortDirection ParsePortDirection(const SymbolTableNode& node);

  // Parses port width from symbol table node
  // Args:
  //   node: The symbol table node
  // Returns:
  //   Bit width (-1 if unknown)
  int ParsePortWidth(const SymbolTableNode& node);

  // Adds an error message
  void AddError(std::string_view message);

  // Adds a warning message
  void AddWarning(std::string_view message);

  // Helper: Recursively validate module hierarchy
  void ValidateModuleHierarchy(const SymbolTableNode& node);
  
  // Helper to recursively validate with module context tracking
  void ValidateModuleHierarchyWithContext(const SymbolTableNode& node,
                                           const std::string& current_module);

  // Helper to collect all instances in a module
  void CollectModuleInstances(const SymbolTableNode& module_node,
                               std::string_view module_name,
                               std::map<std::string, std::vector<std::string>>& signal_drivers);

  // Helper to validate a single instance
  void ValidateSingleInstance(const SymbolTableNode& instance_node,
                               std::string_view instance_name,
                               std::string_view parent_module);

  // Helper to validate a single instance and track output drivers
  void ValidateSingleInstanceAndTrackDrivers(
      const SymbolTableNode& instance_node,
      std::string_view instance_name,
      std::string_view parent_module,
      std::map<std::string, std::vector<std::string>>& signal_drivers);
  
  // Helper: Validate all instances within a module
  void ValidateModuleInstances(const SymbolTableNode& module_node,
                                std::string_view module_name);
  
  // Helper: Find a module definition by name
  const SymbolTableNode* FindModuleDefinition(std::string_view module_name) const;
  
  // Helper: Recursive search for module in node tree
  const SymbolTableNode* FindModuleInNode(const SymbolTableNode& node,
                                           std::string_view module_name) const;

  const SymbolTable* symbol_table_;  // Not owned
  std::vector<std::string> errors_;
  std::vector<std::string> warnings_;
};

}  // namespace analysis
}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_PORT_CONNECTION_VALIDATOR_H_

