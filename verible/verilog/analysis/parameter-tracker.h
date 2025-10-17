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

// ParameterTracker tracks and validates SystemVerilog parameters throughout
// a design hierarchy.

#ifndef VERIBLE_VERILOG_ANALYSIS_PARAMETER_TRACKER_H_
#define VERIBLE_VERILOG_ANALYSIS_PARAMETER_TRACKER_H_

#include <map>
#include <string>
#include <string_view>
#include <vector>

#include "absl/status/status.h"
#include "verible/common/text/symbol.h"
#include "verible/verilog/analysis/symbol-table.h"

namespace verilog {
namespace analysis {

// Represents a parameter override in a module instantiation
struct ParameterOverride {
  std::string instance_name;       // Name of the module instance
  std::string new_value;           // Overridden value as string
  const verible::Symbol* syntax_origin = nullptr;

  ParameterOverride(std::string_view inst, std::string_view val)
      : instance_name(inst), new_value(val) {}
};

// Represents a parameter definition
struct ParameterInfo {
  std::string name;                    // Parameter name
  bool is_localparam = false;          // true if localparam, false if parameter
  std::string type;                    // Parameter type (int, string, etc.)
  std::string default_value;           // Default value as string
  std::vector<ParameterOverride> overrides;  // All overrides of this parameter
  const SymbolTableNode* node = nullptr;     // Symbol table node
  const verible::Symbol* syntax_origin = nullptr;

  ParameterInfo() = default;
  explicit ParameterInfo(std::string_view n) : name(n) {}
  
  // Check if this parameter can be overridden
  bool CanBeOverridden() const { return !is_localparam; }
  
  // Add an override to this parameter
  void AddOverride(std::string_view instance, std::string_view value) {
    overrides.emplace_back(instance, value);
  }
  
  // Get the effective value for a specific instance
  // Returns default_value if no override exists for that instance
  std::string_view GetEffectiveValue(std::string_view instance_name) const {
    for (const auto& override : overrides) {
      if (override.instance_name == instance_name) {
        return override.new_value;
      }
    }
    return default_value;
  }
};

// ParameterTracker extracts and validates parameter usage throughout a design
class ParameterTracker {
 public:
  // Construct a ParameterTracker with a symbol table
  // Args:
  //   symbol_table: The symbol table to analyze (must not be null)
  explicit ParameterTracker(const SymbolTable* symbol_table)
      : symbol_table_(symbol_table) {}

  // Track all parameters in the design
  // Extracts parameter definitions and overrides
  // Returns:
  //   absl::Status::OK on success, error status otherwise
  absl::Status TrackAllParameters();

  // Validate all parameter usage
  // Checks for:
  //   - Attempts to override localparam
  //   - Missing required parameters
  //   - Type mismatches (if type info available)
  // Returns:
  //   absl::Status::OK if valid, error status with details otherwise
  absl::Status ValidateParameters();

  // Get all tracked parameters
  // Returns:
  //   Map of module_name.param_name -> ParameterInfo
  const std::map<std::string, ParameterInfo>& GetParameters() const {
    return parameters_;
  }

  // Get validation errors
  const std::vector<std::string>& GetErrors() const { return errors_; }

  // Get validation warnings
  const std::vector<std::string>& GetWarnings() const { return warnings_; }

  // Clear all diagnostics
  void ClearDiagnostics() {
    errors_.clear();
    warnings_.clear();
  }

 private:
  // Extract all parameter definitions from the symbol table
  void ExtractParameters();

  // Traverse symbol table to find modules
  void TraverseForModules(const SymbolTableNode& node);

  // Extract parameters from a module's CST
  // Args:
  //   module_symbol: CST node for the module
  //   module_name: Name of the module
  void ExtractParametersFromModule(const verible::Symbol& module_symbol,
                                  std::string_view module_name);

  // Traverse symbol table to find parameter definitions (DEPRECATED)
  // Args:
  //   node: Current symbol table node
  //   module_context: Current module name (for scoping)
  void TraverseForParameters(const SymbolTableNode& node,
                            std::string_view module_context);

  // Extract parameter definition from a symbol table node
  // Args:
  //   node: Symbol table node representing the parameter
  //   param_name: Name of the parameter
  //   module_context: Module containing this parameter
  // Returns:
  //   ParameterInfo structure with parameter details
  ParameterInfo ExtractParameterDefinition(const SymbolTableNode& node,
                                          std::string_view param_name,
                                          std::string_view module_context);

  // Extract all parameter overrides from module instantiations
  void ExtractOverrides();

  // Traverse symbol table to find parameter overrides in instantiations
  // Args:
  //   node: Current symbol table node
  //   module_context: Current module name
  void TraverseForOverrides(const SymbolTableNode& node,
                           std::string_view module_context);

  // Validate that a parameter override is legal
  // Args:
  //   module_name: Name of module being instantiated
  //   param_name: Name of parameter being overridden
  //   instance_name: Name of the module instance
  //   new_value: New value for the parameter
  // Returns:
  //   true if override is valid, false otherwise
  bool ValidateParameterOverride(std::string_view module_name,
                                 std::string_view param_name,
                                 std::string_view instance_name,
                                 std::string_view new_value);

  // Check if a parameter exists and can be overridden
  // Args:
  //   module_name: Module containing the parameter
  //   param_name: Parameter name
  // Returns:
  //   Pointer to ParameterInfo if found, nullptr otherwise
  const ParameterInfo* FindParameter(std::string_view module_name,
                                    std::string_view param_name) const;

  // Parse parameter type from symbol table info
  // Args:
  //   node: Symbol table node
  // Returns:
  //   Type string (e.g., "int", "logic", "string")
  std::string ParseParameterType(const SymbolTableNode& node) const;

  // Parse parameter default value from symbol table or CST
  // Args:
  //   node: Symbol table node
  // Returns:
  //   Default value as string
  std::string ParseParameterValue(const SymbolTableNode& node) const;

  // Add an error message
  void AddError(std::string_view message);

  // Add a warning message
  void AddWarning(std::string_view message);

  // Symbol table to analyze
  const SymbolTable* symbol_table_;

  // Map of "module.parameter" -> ParameterInfo
  std::map<std::string, ParameterInfo> parameters_;

  // Validation errors
  std::vector<std::string> errors_;

  // Validation warnings
  std::vector<std::string> warnings_;
};

}  // namespace analysis
}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_PARAMETER_TRACKER_H_

