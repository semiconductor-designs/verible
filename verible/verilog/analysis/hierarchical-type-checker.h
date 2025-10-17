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

#ifndef VERIBLE_VERILOG_ANALYSIS_HIERARCHICAL_TYPE_CHECKER_H_
#define VERIBLE_VERILOG_ANALYSIS_HIERARCHICAL_TYPE_CHECKER_H_

#include <map>
#include <string>
#include <vector>

#include "verible/common/text/symbol.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace analysis {

// Forward declarations
class HierarchicalTypeChecker;

// Represents a node in the type hierarchy tree
struct TypeHierarchyNode {
  std::string type_name;                          // Name of the type (class/interface/module)
  std::string base_type;                          // Name of base type (for inheritance)
  const VerilogSourceFile* file = nullptr;        // Source file containing this type
  const verible::Symbol* syntax_origin = nullptr; // CST node for this type
  std::vector<TypeHierarchyNode*> derived_types;  // Types that extend/inherit from this
  bool is_class = false;                          // True if this is a class
  bool is_interface = false;                      // True if this is an interface
  bool is_module = false;                         // True if this is a module
  
  TypeHierarchyNode() = default;
  
  TypeHierarchyNode(const std::string& name, bool cls, bool iface, bool mod)
      : type_name(name), is_class(cls), is_interface(iface), is_module(mod) {}
};

// Information about an inheritance relationship
struct InheritanceInfo {
  std::string derived_name;                       // Name of derived class/interface
  std::string base_name;                          // Name of base class/interface
  const verible::Symbol* syntax_origin = nullptr; // CST node for extends declaration
  bool is_valid = true;                           // False if errors detected
  std::string error_message;                      // Error description if invalid
  
  InheritanceInfo() = default;
  
  InheritanceInfo(const std::string& derived, const std::string& base,
                  const verible::Symbol* origin = nullptr)
      : derived_name(derived), base_name(base), syntax_origin(origin) {}
};

// Result of type compatibility check
struct TypeCompatibilityResult {
  bool compatible = false;                        // True if types are compatible
  std::string reason;                             // Explanation of compatibility/incompatibility
  const verible::Symbol* location = nullptr;      // Location of type usage
  
  TypeCompatibilityResult() = default;
  
  TypeCompatibilityResult(bool compat, const std::string& msg,
                         const verible::Symbol* loc = nullptr)
      : compatible(compat), reason(msg), location(loc) {}
};

// Main hierarchical type checker class
// Validates type hierarchies, inheritance relationships, and cross-module type compatibility
class HierarchicalTypeChecker {
 public:
  // Constructor
  // @param symbol_table The symbol table built from parsed source files
  // @param project The Verilog project containing all source files
  HierarchicalTypeChecker(const SymbolTable& symbol_table,
                         const VerilogProject& project);
  
  // Main validation entry points
  
  // Validate the entire type hierarchy
  // Builds the hierarchy tree and performs all validations
  void ValidateHierarchy();
  
  // Validate all inheritance relationships
  // Checks for circular inheritance, missing base types, etc.
  void ValidateInheritance();
  
  // Validate type compatibility across module boundaries
  // Checks struct field matching, typedef resolution, etc.
  void ValidateTypeCompatibility();
  
  // Getters for results
  
  // Get all error messages detected
  const std::vector<std::string>& GetErrors() const { return errors_; }
  
  // Get all warning messages
  const std::vector<std::string>& GetWarnings() const { return warnings_; }
  
  // Get the constructed type hierarchy
  const std::map<std::string, TypeHierarchyNode>& GetTypeHierarchy() const {
    return type_hierarchy_;
  }
  
  // Get all inheritance relationships found
  const std::vector<InheritanceInfo>& GetInheritanceInfo() const {
    return inheritance_info_;
  }
  
 private:
  // Type hierarchy building
  
  // Build the complete type hierarchy tree
  void BuildTypeHierarchy();
  
  // Extract class hierarchy from symbol table
  void ExtractClassHierarchy();
  
  // Extract interface hierarchy from symbol table
  void ExtractInterfaceHierarchy();
  
  // Extract module instantiation hierarchy
  void ExtractModuleHierarchy();
  
  // Recursively traverse symbol table to find all types
  void TraverseSymbolTable(const SymbolTableNode& node);
  
  // Inheritance validation
  
  // Validate all class inheritance relationships
  void ValidateClassInheritance();
  
  // Validate all interface inheritance relationships
  void ValidateInterfaceInheritance();
  
  // Detect circular inheritance starting from a node
  // @param node The starting node to check
  // @param visited Set of already visited nodes (to detect cycles)
  // @return True if circular inheritance detected
  bool DetectCircularInheritance(const TypeHierarchyNode& node,
                                std::vector<std::string>& visited);
  
  // Check if a base class/interface exists
  // @param base_name Name of the base type
  // @param derived_name Name of the derived type (for error messages)
  // @param location CST location for error reporting
  // @return True if base type exists
  bool CheckBaseExists(const std::string& base_name,
                      const std::string& derived_name,
                      const verible::Symbol* location);
  
  // Type compatibility checking
  
  // Check if two types are compatible
  // @param type1 First type name
  // @param type2 Second type name
  // @param location CST location for error reporting
  // @return TypeCompatibilityResult with details
  TypeCompatibilityResult CheckTypeCompatibility(const std::string& type1,
                                                const std::string& type2,
                                                const verible::Symbol* location);
  
  // Check struct field-by-field compatibility
  // @param s1 First struct node
  // @param s2 Second struct node
  // @return True if structs are compatible
  bool CheckStructCompatibility(const SymbolTableNode& s1,
                               const SymbolTableNode& s2);
  
  // Resolve typedef to underlying type
  // @param typedef_name Name of the typedef
  // @return Name of underlying type, or empty if not found
  std::string ResolveTypedef(const std::string& typedef_name);
  
  // Helper methods
  
  // Find a type node in the hierarchy
  // @param type_name Name of the type to find
  // @return Pointer to node, or nullptr if not found
  TypeHierarchyNode* FindTypeNode(const std::string& type_name);
  
  // Check if a name is a class
  bool IsClass(const std::string& type_name) const;
  
  // Check if a name is an interface
  bool IsInterface(const std::string& type_name) const;
  
  // Check if a name is a module
  bool IsModule(const std::string& type_name) const;
  
  // Error and warning reporting
  
  // Add an error message
  // @param message Error description
  // @param location Optional CST location
  void AddError(const std::string& message,
               const verible::Symbol* location = nullptr);
  
  // Add a warning message
  // @param message Warning description
  // @param location Optional CST location
  void AddWarning(const std::string& message,
                 const verible::Symbol* location = nullptr);
  
  // Format a message with file/line information
  // @param message The message text
  // @param location CST location
  // @return Formatted message string
  std::string FormatMessage(const std::string& message,
                           const verible::Symbol* location) const;
  
  // Data members
  const SymbolTable& symbol_table_;                      // Reference to symbol table
  const VerilogProject& project_;                        // Reference to project
  std::map<std::string, TypeHierarchyNode> type_hierarchy_; // Type hierarchy tree
  std::vector<InheritanceInfo> inheritance_info_;        // All inheritance relationships
  std::vector<std::string> errors_;                      // Error messages
  std::vector<std::string> warnings_;                    // Warning messages
};

}  // namespace analysis
}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_HIERARCHICAL_TYPE_CHECKER_H_

