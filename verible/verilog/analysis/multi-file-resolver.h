// Copyright 2025 The Verible Authors.
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

#ifndef VERIBLE_VERILOG_ANALYSIS_MULTI_FILE_RESOLVER_H_
#define VERIBLE_VERILOG_ANALYSIS_MULTI_FILE_RESOLVER_H_

#include <map>
#include <set>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "verible/verilog/analysis/symbol-table.h"

namespace verilog {
namespace analysis {

// Represents a module instance in the design hierarchy.
struct ModuleInstance {
  std::string instance_name;     // Name of the instance (e.g., "u_module_b")
  std::string module_type;       // Type of module (e.g., "module_b")
  std::string parent_module;     // Parent module name
  const verible::Symbol* symbol; // AST node of the instance
  
  ModuleInstance() : symbol(nullptr) {}
  
  ModuleInstance(std::string_view inst_name,
                 std::string_view mod_type,
                 std::string_view parent,
                 const verible::Symbol* sym)
      : instance_name(inst_name),
        module_type(mod_type),
        parent_module(parent),
        symbol(sym) {}
};

// Represents a dependency relationship between modules.
struct ModuleDependency {
  std::string from_module;  // Module that has the dependency
  std::string to_module;    // Module being depended upon
  
  ModuleDependency(std::string_view from, std::string_view to)
      : from_module(from), to_module(to) {}
  
  bool operator<(const ModuleDependency& other) const {
    if (from_module != other.from_module) {
      return from_module < other.from_module;
    }
    return to_module < other.to_module;
  }
};

// Dependency graph for module hierarchy.
class DependencyGraph {
 public:
  DependencyGraph() = default;
  
  // Add a dependency edge
  void AddDependency(std::string_view from, std::string_view to);
  
  // Check if a dependency exists
  bool HasDependency(std::string_view from, std::string_view to) const;
  
  // Get all modules that 'module' depends on
  std::vector<std::string> GetDependencies(std::string_view module) const;
  
  // Get all modules that depend on 'module'
  std::vector<std::string> GetDependents(std::string_view module) const;
  
  // Get all modules in the graph
  std::set<std::string> GetAllModules() const;
  
  // Detect circular dependencies
  // Returns list of cycles, where each cycle is a list of module names
  std::vector<std::vector<std::string>> DetectCircularDependencies() const;
  
  // Check if graph has cycles
  bool HasCycles() const;
  
  // Get topological order (if no cycles)
  // Returns empty vector if cycles exist
  std::vector<std::string> GetTopologicalOrder() const;
  
 private:
  // Adjacency list: module -> set of modules it depends on
  std::map<std::string, std::set<std::string>> dependencies_;
  
  // Reverse adjacency list: module -> set of modules that depend on it
  std::map<std::string, std::set<std::string>> dependents_;
  
  // Helper for cycle detection using DFS
  bool HasCyclesDFS(const std::string& module,
                    std::set<std::string>* visited,
                    std::set<std::string>* rec_stack,
                    std::vector<std::string>* current_path,
                    std::vector<std::vector<std::string>>* cycles) const;
};

// MultiFileResolver handles cross-file symbol resolution and module hierarchy.
//
// This class provides functionality to:
// 1. Resolve module definitions across multiple files
// 2. Track module instantiations
// 3. Build and analyze dependency graphs
// 4. Detect circular dependencies
// 5. Validate cross-module references
//
// Example usage:
//   SymbolTable symbol_table;
//   // ... populate symbol table with multiple files ...
//   
//   MultiFileResolver resolver(&symbol_table);
//   absl::Status status = resolver.ResolveReferences();
//   if (!status.ok()) {
//     // Handle resolution errors
//   }
//   
//   // Get module definition
//   const SymbolTableNode* mod = resolver.GetModuleDefinition("my_module");
//   
//   // Check for circular dependencies
//   if (resolver.HasCircularDependencies()) {
//     auto cycles = resolver.GetCircularDependencies();
//     // Handle cycles
//   }
class MultiFileResolver {
 public:
  // Construct resolver for given symbol table
  explicit MultiFileResolver(const SymbolTable* symbol_table);
  
  // Resolve all cross-file references
  // This builds the internal module definition map and dependency graph
  absl::Status ResolveReferences();
  
  // Get module definition by name
  // Returns nullptr if module not found
  const SymbolTableNode* GetModuleDefinition(std::string_view module_name) const;
  
  // Check if a module definition exists
  bool HasModuleDefinition(std::string_view module_name) const;
  
  // Get all module names defined in the symbol table
  std::vector<std::string> GetAllModuleNames() const;
  
  // Get all instances of a specific module type
  std::vector<ModuleInstance> GetModuleInstances(std::string_view module_type) const;
  
  // Get all instances within a specific parent module
  std::vector<ModuleInstance> GetInstancesInModule(std::string_view parent_module) const;
  
  // Get all module instances (across all modules)
  const std::vector<ModuleInstance>& GetAllInstances() const { return instances_; }
  
  // Build dependency graph from module instantiations
  absl::Status BuildDependencyGraph();
  
  // Get the dependency graph
  const DependencyGraph& GetDependencyGraph() const { return dependency_graph_; }
  
  // Check if there are circular dependencies
  bool HasCircularDependencies() const;
  
  // Get all circular dependency cycles
  std::vector<std::vector<std::string>> GetCircularDependencies() const;
  
  // Validate that all module instantiations reference defined modules
  absl::Status ValidateModuleReferences();
  
  // Get list of undefined modules (referenced but not defined)
  std::vector<std::string> GetUndefinedModules() const;
  
 private:
  const SymbolTable* symbol_table_;
  
  // Map of module name -> module definition node
  std::map<std::string, const SymbolTableNode*> module_definitions_;
  
  // List of all module instances found
  std::vector<ModuleInstance> instances_;
  
  // Dependency graph
  DependencyGraph dependency_graph_;
  
  // Helper: Extract module definitions from symbol table
  void ExtractModuleDefinitions();
  
  // Helper: Recursively extract module definitions from a node
  void ExtractModuleDefinitionsFromNode(const SymbolTableNode& node);
  
  // Helper: Extract module instances from symbol table
  void ExtractModuleInstances();
  
  // Helper: Recursively extract module instances from a node
  void ExtractModuleInstancesFromNode(const SymbolTableNode& node,
                                      const std::string& parent_module);
  
  // Helper: Build dependency graph from instances
  void BuildDependencyGraphInternal();
};

}  // namespace analysis
}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_MULTI_FILE_RESOLVER_H_

