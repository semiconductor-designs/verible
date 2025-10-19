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

#include "verible/verilog/analysis/hierarchical-type-checker.h"

#include <algorithm>
#include <sstream>
#include <string>
#include <vector>

#include "verible/common/analysis/syntax-tree-search.h"
#include "verible/common/text/concrete-syntax-leaf.h"
#include "verible/common/text/concrete-syntax-tree.h"
#include "verible/common/text/symbol.h"
#include "verible/common/text/token-info.h"
#include "verible/common/text/tree-utils.h"
#include "verible/verilog/CST/class.h"
#include "verible/verilog/CST/module.h"
#include "verible/verilog/CST/verilog-matchers.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace analysis {

// Constructor
HierarchicalTypeChecker::HierarchicalTypeChecker(
    const SymbolTable& symbol_table,
    const VerilogProject& project)
    : symbol_table_(symbol_table),
      project_(project) {
}

// Main validation entry points

void HierarchicalTypeChecker::ValidateHierarchy() {
  // Build the type hierarchy tree
  BuildTypeHierarchy();
  
  // Validate all inheritance relationships
  ValidateInheritance();
  
  // Validate type compatibility
  ValidateTypeCompatibility();
}

void HierarchicalTypeChecker::ValidateInheritance() {
  // Validate class inheritance
  ValidateClassInheritance();
  
  // Validate interface inheritance
  ValidateInterfaceInheritance();
}

void HierarchicalTypeChecker::ValidateTypeCompatibility() {
  // TODO: Implement type compatibility validation
  // This will check struct field matching, typedef resolution, etc.
}

// Type hierarchy building

void HierarchicalTypeChecker::BuildTypeHierarchy() {
  // Traverse the symbol table to extract all types
  TraverseSymbolTable(symbol_table_.Root());
  
  // Extract class hierarchy (extends relationships)
  ExtractClassHierarchy();
  
  // Extract interface hierarchy
  ExtractInterfaceHierarchy();
  
  // Extract module instantiation hierarchy
  ExtractModuleHierarchy();
}

void HierarchicalTypeChecker::TraverseSymbolTable(const SymbolTableNode& node) {
  // Get the node's metatype
  const auto metatype = node.Value().metatype;
  
  // Check if this is a class, interface, or module
  if (metatype == SymbolMetaType::kClass ||
      metatype == SymbolMetaType::kInterface ||
      metatype == SymbolMetaType::kModule) {
    
    // Get the type name
    const auto* key = node.Key();
    if (!key) return;
    
    std::string type_name(*key);
    
    // Determine the type flags
    bool is_class = (metatype == SymbolMetaType::kClass);
    bool is_interface = (metatype == SymbolMetaType::kInterface);
    bool is_module = (metatype == SymbolMetaType::kModule);
    
    // Create a hierarchy node
    TypeHierarchyNode type_node(type_name, is_class, is_interface, is_module);
    
    // Get syntax origin for this type
    type_node.syntax_origin = node.Value().syntax_origin;
    
    // Get source file
    type_node.file = node.Value().file_origin;
    
    // Add to hierarchy
    type_hierarchy_[type_name] = type_node;
  }
  
  // Recursively traverse children
  for (const auto& [child_name, child_node] : node) {
    TraverseSymbolTable(child_node);
  }
}

void HierarchicalTypeChecker::ExtractClassHierarchy() {
  // Iterate through all types in hierarchy and check symbol table for base types
  for (const auto& [type_name, child_node] : symbol_table_.Root()) {
    // Find this type in our hierarchy
    auto type_it = type_hierarchy_.find(std::string(*child_node.Key()));
    if (type_it == type_hierarchy_.end()) continue;
    
    auto& type_node = type_it->second;
    if (!type_node.is_class && !type_node.is_interface) continue;
    
    // Check if this type has a parent type (base class/interface)
    const auto& parent_type = child_node.Value().parent_type;
    if (!parent_type.user_defined_type) continue;
    
    // Extract the base type name from the user_defined_type
    const auto& ref_comp = parent_type.user_defined_type->Value();
    if (ref_comp.identifier.empty()) continue;
    
    std::string base_type_name(ref_comp.identifier);
    
    // Set the base type in our hierarchy node
    type_node.base_type = base_type_name;
    
    // Record this inheritance relationship
    InheritanceInfo info(std::string(type_name), base_type_name, type_node.syntax_origin);
    inheritance_info_.push_back(info);
    
    // If base type exists, add this type as a derived type
    auto base_it = type_hierarchy_.find(base_type_name);
    if (base_it != type_hierarchy_.end()) {
      base_it->second.derived_types.push_back(&type_node);
    }
  }
}

void HierarchicalTypeChecker::ExtractInterfaceHierarchy() {
  // Interface extends is now handled in ExtractClassHierarchy()
  // Both classes and interfaces use the same parent_type mechanism in the symbol table
  // No additional work needed here
}

void HierarchicalTypeChecker::ExtractModuleHierarchy() {
  // Extract module instantiation relationships
  // TODO: Implement module hierarchy extraction
}

// Inheritance validation

void HierarchicalTypeChecker::ValidateClassInheritance() {
  // Check each class in the hierarchy
  for (const auto& [type_name, type_node] : type_hierarchy_) {
    if (!type_node.is_class) continue;
    
    // If this class has a base class, validate the inheritance
    if (!type_node.base_type.empty()) {
      // Check if base class exists
      if (!CheckBaseExists(type_node.base_type, type_name,
                          type_node.syntax_origin)) {
        continue;  // Error already reported
      }
      
      // Check for circular inheritance
      std::vector<std::string> visited;
      visited.push_back(type_name);
      
      if (DetectCircularInheritance(type_node, visited)) {
        // Build cycle path string
        std::string cycle_path;
        for (size_t i = 0; i < visited.size(); ++i) {
          if (i > 0) cycle_path += " -> ";
          cycle_path += visited[i];
        }
        
        AddError("Circular inheritance detected: " + cycle_path,
                type_node.syntax_origin);
      }
    }
  }
}

void HierarchicalTypeChecker::ValidateInterfaceInheritance() {
  // Similar to ValidateClassInheritance but for interfaces
  for (const auto& [type_name, type_node] : type_hierarchy_) {
    if (!type_node.is_interface) continue;
    
    // If this interface has a base interface, validate
    if (!type_node.base_type.empty()) {
      // Check if base interface exists
      if (!CheckBaseExists(type_node.base_type, type_name,
                          type_node.syntax_origin)) {
        continue;  // Error already reported
      }
      
      // Check for circular inheritance
      std::vector<std::string> visited;
      visited.push_back(type_name);
      
      if (DetectCircularInheritance(type_node, visited)) {
        std::string cycle_path;
        for (size_t i = 0; i < visited.size(); ++i) {
          if (i > 0) cycle_path += " -> ";
          cycle_path += visited[i];
        }
        
        AddError("Circular interface inheritance detected: " + cycle_path,
                type_node.syntax_origin);
      }
    }
  }
}

bool HierarchicalTypeChecker::DetectCircularInheritance(
    const TypeHierarchyNode& node,
    std::vector<std::string>& visited) {
  
  // If no base type, no cycle
  if (node.base_type.empty()) {
    return false;
  }
  
  // Check if we've already visited this base type (cycle detected)
  if (std::find(visited.begin(), visited.end(), node.base_type) != visited.end()) {
    visited.push_back(node.base_type);  // Complete the cycle for error message
    return true;
  }
  
  // Find the base type node
  auto it = type_hierarchy_.find(node.base_type);
  if (it == type_hierarchy_.end()) {
    // Base type not found (error reported elsewhere)
    return false;
  }
  
  // Add to visited and recurse
  visited.push_back(node.base_type);
  return DetectCircularInheritance(it->second, visited);
}

bool HierarchicalTypeChecker::CheckBaseExists(
    const std::string& base_name,
    const std::string& derived_name,
    const verible::Symbol* location) {
  
  auto it = type_hierarchy_.find(base_name);
  if (it == type_hierarchy_.end()) {
    AddError("Base type '" + base_name + "' not found for '" +
            derived_name + "'", location);
    return false;
  }
  
  return true;
}

// Type compatibility checking

TypeCompatibilityResult HierarchicalTypeChecker::CheckTypeCompatibility(
    const std::string& type1,
    const std::string& type2,
    const verible::Symbol* location) {
  
  // If types are identical, they're compatible
  if (type1 == type2) {
    return TypeCompatibilityResult(true, "Types are identical", location);
  }
  
  // TODO: Implement more sophisticated type checking
  // - Typedef resolution
  // - Struct field matching
  // - Packed/unpacked compatibility
  
  return TypeCompatibilityResult(false, "Type mismatch", location);
}

bool HierarchicalTypeChecker::CheckStructCompatibility(
    const SymbolTableNode& s1,
    const SymbolTableNode& s2) {
  
  // TODO: Implement struct field-by-field comparison
  // - Check field names match
  // - Check field types match
  // - Check field order matches
  
  return false;
}

std::string HierarchicalTypeChecker::ResolveTypedef(
    const std::string& typedef_name) {
  
  // TODO: Implement typedef resolution
  // Search symbol table for typedef and return underlying type
  
  return "";
}

// Helper methods

TypeHierarchyNode* HierarchicalTypeChecker::FindTypeNode(
    const std::string& type_name) {
  
  auto it = type_hierarchy_.find(type_name);
  if (it != type_hierarchy_.end()) {
    return &it->second;
  }
  return nullptr;
}

bool HierarchicalTypeChecker::IsClass(const std::string& type_name) const {
  auto it = type_hierarchy_.find(type_name);
  return it != type_hierarchy_.end() && it->second.is_class;
}

bool HierarchicalTypeChecker::IsInterface(const std::string& type_name) const {
  auto it = type_hierarchy_.find(type_name);
  return it != type_hierarchy_.end() && it->second.is_interface;
}

bool HierarchicalTypeChecker::IsModule(const std::string& type_name) const {
  auto it = type_hierarchy_.find(type_name);
  return it != type_hierarchy_.end() && it->second.is_module;
}

// Error and warning reporting

void HierarchicalTypeChecker::AddError(const std::string& message,
                                      const verible::Symbol* location) {
  errors_.push_back(FormatMessage(message, location));
}

void HierarchicalTypeChecker::AddWarning(const std::string& message,
                                        const verible::Symbol* location) {
  warnings_.push_back(FormatMessage(message, location));
}

std::string HierarchicalTypeChecker::FormatMessage(
    const std::string& message,
    const verible::Symbol* location) const {
  
  if (!location) {
    return message;
  }
  
  // TODO: Extract file/line information from location
  // For now, just return the message
  return message;
}

}  // namespace analysis
}  // namespace verilog

