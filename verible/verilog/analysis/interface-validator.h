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

#ifndef VERIBLE_VERILOG_ANALYSIS_INTERFACE_VALIDATOR_H_
#define VERIBLE_VERILOG_ANALYSIS_INTERFACE_VALIDATOR_H_

#include <map>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "absl/status/status.h"
#include "verible/common/text/symbol.h"
#include "verible/verilog/analysis/symbol-table.h"

namespace verilog {
namespace analysis {

// SymbolTable and SymbolTableNode are defined in symbol-table.h
// They are already in verilog namespace, so we can use them directly

// Direction of a signal in a modport
enum class ModportDirection {
  kInput,
  kOutput,
  kInout,
  kRef,
  kUnknown
};

// Represents a signal within an interface
struct InterfaceSignal {
  std::string name;
  std::string type;  // e.g., "logic", "logic [7:0]"
  int width = -1;    // -1 for unknown/scalar
  const verible::Symbol* syntax_origin = nullptr;

  InterfaceSignal(std::string_view n, std::string_view t)
      : name(n), type(t) {}
};

// Represents a modport within an interface
struct ModportInfo {
  std::string name;
  std::map<std::string, ModportDirection> signals;  // signal_name -> direction
  const verible::Symbol* syntax_origin = nullptr;

  explicit ModportInfo(std::string_view n) : name(n) {}
  
  // Add a signal to this modport
  void AddSignal(std::string_view signal_name, ModportDirection dir) {
    signals[std::string(signal_name)] = dir;
  }
  
  // Get direction of a signal in this modport
  std::optional<ModportDirection> GetSignalDirection(std::string_view signal_name) const {
    auto it = signals.find(std::string(signal_name));
    if (it != signals.end()) {
      return it->second;
    }
    return std::nullopt;
  }
};

// Represents an interface definition
struct InterfaceInfo {
  std::string name;
  std::vector<InterfaceSignal> signals;
  std::vector<ModportInfo> modports;
  std::map<std::string, std::string> parameters;  // param_name -> default_value
  const SymbolTableNode* node = nullptr;
  const verible::Symbol* syntax_origin = nullptr;

  explicit InterfaceInfo(std::string_view n) : name(n) {}
  
  // Find a modport by name
  const ModportInfo* FindModport(std::string_view modport_name) const {
    for (const auto& mp : modports) {
      if (mp.name == modport_name) {
        return &mp;
      }
    }
    return nullptr;
  }
  
  // Find a signal by name
  const InterfaceSignal* FindSignal(std::string_view signal_name) const {
    for (const auto& sig : signals) {
      if (sig.name == signal_name) {
        return &sig;
      }
    }
    return nullptr;
  }
};

// Represents a connection to an interface
struct InterfaceConnection {
  std::string instance_name;      // Name of the interface instance
  std::string interface_type;     // Type of interface
  std::string modport_name;       // Modport used (if any)
  std::string module_name;        // Module using the interface
  const InterfaceInfo* interface_def = nullptr;
  const verible::Symbol* syntax_origin = nullptr;

  InterfaceConnection(std::string_view inst, std::string_view intf_type,
                      std::string_view mp, std::string_view mod)
      : instance_name(inst), interface_type(intf_type),
        modport_name(mp), module_name(mod) {}
};

// Validates SystemVerilog interface usage including:
// - Interface definitions
// - Modport declarations
// - Interface instantiation
// - Interface port connections
// - Modport compatibility
// - Signal direction checking
//
// Usage:
//   InterfaceValidator validator(symbol_table);
//   absl::Status status = validator.ValidateAllInterfaces();
//   if (!status.ok()) {
//     for (const auto& error : validator.GetErrors()) {
//       std::cerr << error << std::endl;
//     }
//   }
class InterfaceValidator {
 public:
  // Constructor
  // Args:
  //   symbol_table: The symbol table containing interface definitions
  explicit InterfaceValidator(const SymbolTable* symbol_table);

  // Validates all interface usage in the symbol table
  // Returns:
  //   absl::Status::OK if all interfaces are valid, error status otherwise
  absl::Status ValidateAllInterfaces();

  // Validates a specific interface connection
  // Args:
  //   connection: The interface connection to validate
  // Returns:
  //   absl::Status::OK if connection is valid, error status otherwise
  absl::Status ValidateInterfaceConnection(const InterfaceConnection& connection);

  // Validates modport usage in a module
  // Args:
  //   interface_name: Name of the interface
  //   modport_name: Name of the modport
  //   module_name: Name of the module using the modport
  // Returns:
  //   true if modport usage is valid, false otherwise
  bool ValidateModportUsage(std::string_view interface_name,
                            std::string_view modport_name,
                            std::string_view module_name);

  // Gets all validation errors
  const std::vector<std::string>& GetErrors() const { return errors_; }

  // Gets all validation warnings
  const std::vector<std::string>& GetWarnings() const { return warnings_; }

  // Gets all detected interfaces
  const std::map<std::string, InterfaceInfo>& GetInterfaces() const {
    return interfaces_;
  }

  // Clears all errors and warnings
  void ClearDiagnostics() {
    errors_.clear();
    warnings_.clear();
  }

 private:
  // Extracts all interface definitions from the symbol table
  void ExtractInterfaces();

  // Extracts interface definition from a symbol table node
  // Args:
  //   node: The symbol table node representing the interface
  // Returns:
  //   InterfaceInfo structure with interface details
  InterfaceInfo ExtractInterfaceDefinition(const SymbolTableNode& node,
                                            std::string_view interface_name);

  // Extracts modports from an interface node
  // Args:
  //   node: The symbol table node representing the interface
  // Returns:
  //   Vector of ModportInfo structures
  std::vector<ModportInfo> ExtractModports(const SymbolTableNode& node);

  // Extracts signals from an interface node
  // Args:
  //   node: The symbol table node representing the interface
  // Returns:
  //   Vector of InterfaceSignal structures
  std::vector<InterfaceSignal> ExtractSignals(const SymbolTableNode& node);

  // Extracts all interface connections from the symbol table
  void ExtractConnections();

  // Validates that a modport exists in an interface
  // Args:
  //   interface_info: The interface to check
  //   modport_name: Name of the modport to find
  // Returns:
  //   true if modport exists, false otherwise
  bool ModportExists(const InterfaceInfo& interface_info,
                     std::string_view modport_name) const;

  // Checks signal compatibility between interface and modport usage
  // Args:
  //   interface_info: The interface definition
  //   modport_name: The modport being used
  //   usage_context: Context of usage (read/write)
  // Returns:
  //   true if compatible, false otherwise
  bool CheckSignalCompatibility(const InterfaceInfo& interface_info,
                                 std::string_view modport_name,
                                 std::string_view usage_context);

  // Parses modport direction from string
  // Args:
  //   direction_str: String representation of direction
  // Returns:
  //   ModportDirection enum value
  ModportDirection ParseModportDirection(std::string_view direction_str);

  // Adds an error message
  void AddError(std::string_view message);

  // Adds a warning message
  void AddWarning(std::string_view message);

  // Helper: Recursively traverse symbol table for interfaces
  void TraverseForInterfaces(const SymbolTableNode& node);

  // Helper: Recursively traverse symbol table for connections
  void TraverseForConnections(const SymbolTableNode& node,
                               std::string_view current_module);

  const SymbolTable* symbol_table_;
  std::map<std::string, InterfaceInfo> interfaces_;  // interface_name -> InterfaceInfo
  std::vector<InterfaceConnection> connections_;
  std::vector<std::string> errors_;
  std::vector<std::string> warnings_;
};

}  // namespace analysis
}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_INTERFACE_VALIDATOR_H_

