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

#include "verible/verilog/analysis/multi-file-resolver.h"

#include <algorithm>
#include <map>
#include <queue>
#include <set>
#include <stack>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"

namespace verilog {
namespace analysis {

// ============================================================================
// DependencyGraph Implementation
// ============================================================================

void DependencyGraph::AddDependency(std::string_view from, std::string_view to) {
  std::string from_str(from);
  std::string to_str(to);
  
  dependencies_[from_str].insert(to_str);
  dependents_[to_str].insert(from_str);
  
  // Ensure both nodes exist in the graph
  if (dependencies_.find(to_str) == dependencies_.end()) {
    dependencies_[to_str] = std::set<std::string>();
  }
  if (dependents_.find(from_str) == dependents_.end()) {
    dependents_[from_str] = std::set<std::string>();
  }
}

bool DependencyGraph::HasDependency(std::string_view from, std::string_view to) const {
  auto it = dependencies_.find(std::string(from));
  if (it == dependencies_.end()) {
    return false;
  }
  return it->second.count(std::string(to)) > 0;
}

std::vector<std::string> DependencyGraph::GetDependencies(std::string_view module) const {
  auto it = dependencies_.find(std::string(module));
  if (it == dependencies_.end()) {
    return {};
  }
  return std::vector<std::string>(it->second.begin(), it->second.end());
}

std::vector<std::string> DependencyGraph::GetDependents(std::string_view module) const {
  auto it = dependents_.find(std::string(module));
  if (it == dependents_.end()) {
    return {};
  }
  return std::vector<std::string>(it->second.begin(), it->second.end());
}

std::set<std::string> DependencyGraph::GetAllModules() const {
  std::set<std::string> all_modules;
  for (const auto& [module, _] : dependencies_) {
    all_modules.insert(module);
  }
  for (const auto& [module, _] : dependents_) {
    all_modules.insert(module);
  }
  return all_modules;
}

bool DependencyGraph::HasCyclesDFS(
    const std::string& module,
    std::set<std::string>* visited,
    std::set<std::string>* rec_stack,
    std::vector<std::string>* current_path,
    std::vector<std::vector<std::string>>* cycles) const {
  
  visited->insert(module);
  rec_stack->insert(module);
  current_path->push_back(module);
  
  bool found_cycle = false;
  
  // Visit all dependencies
  auto it = dependencies_.find(module);
  if (it != dependencies_.end()) {
    for (const auto& dep : it->second) {
      if (rec_stack->count(dep) > 0) {
        // Found a cycle!
        found_cycle = true;
        
        // Extract the cycle from current_path
        std::vector<std::string> cycle;
        bool in_cycle = false;
        for (const auto& node : *current_path) {
          if (node == dep) {
            in_cycle = true;
          }
          if (in_cycle) {
            cycle.push_back(node);
          }
        }
        cycle.push_back(dep);  // Complete the cycle
        
        if (cycles) {
          cycles->push_back(cycle);
        }
      } else if (visited->count(dep) == 0) {
        if (HasCyclesDFS(dep, visited, rec_stack, current_path, cycles)) {
          found_cycle = true;
        }
      }
    }
  }
  
  rec_stack->erase(module);
  current_path->pop_back();
  
  return found_cycle;
}

std::vector<std::vector<std::string>> DependencyGraph::DetectCircularDependencies() const {
  std::vector<std::vector<std::string>> cycles;
  std::set<std::string> visited;
  std::set<std::string> rec_stack;
  std::vector<std::string> current_path;
  
  auto all_modules = GetAllModules();
  for (const auto& module : all_modules) {
    if (visited.count(module) == 0) {
      HasCyclesDFS(module, &visited, &rec_stack, &current_path, &cycles);
    }
  }
  
  return cycles;
}

bool DependencyGraph::HasCycles() const {
  std::set<std::string> visited;
  std::set<std::string> rec_stack;
  std::vector<std::string> current_path;
  
  auto all_modules = GetAllModules();
  for (const auto& module : all_modules) {
    if (visited.count(module) == 0) {
      if (HasCyclesDFS(module, &visited, &rec_stack, &current_path, nullptr)) {
        return true;
      }
    }
  }
  
  return false;
}

std::vector<std::string> DependencyGraph::GetTopologicalOrder() const {
  if (HasCycles()) {
    return {};  // Cannot do topological sort with cycles
  }
  
  std::vector<std::string> order;
  std::set<std::string> visited;
  std::stack<std::string> stack;
  
  // Helper lambda for DFS
  std::function<void(const std::string&)> dfs = [&](const std::string& module) {
    visited.insert(module);
    
    auto it = dependencies_.find(module);
    if (it != dependencies_.end()) {
      for (const auto& dep : it->second) {
        if (visited.count(dep) == 0) {
          dfs(dep);
        }
      }
    }
    
    stack.push(module);
  };
  
  // Process all modules
  auto all_modules = GetAllModules();
  for (const auto& module : all_modules) {
    if (visited.count(module) == 0) {
      dfs(module);
    }
  }
  
  // Extract from stack (reverse order)
  while (!stack.empty()) {
    order.push_back(stack.top());
    stack.pop();
  }
  
  return order;
}

// ============================================================================
// MultiFileResolver Implementation
// ============================================================================

MultiFileResolver::MultiFileResolver(const SymbolTable* symbol_table)
    : symbol_table_(symbol_table) {}

absl::Status MultiFileResolver::ResolveReferences() {
  if (!symbol_table_) {
    return absl::InvalidArgumentError("Symbol table is null");
  }
  
  // Clear any previous state
  module_definitions_.clear();
  instances_.clear();
  dependency_graph_ = DependencyGraph();
  
  // Extract module definitions from symbol table
  ExtractModuleDefinitions();
  
  // Extract module instances
  ExtractModuleInstances();
  
  return absl::OkStatus();
}

const SymbolTableNode* MultiFileResolver::GetModuleDefinition(
    std::string_view module_name) const {
  auto it = module_definitions_.find(std::string(module_name));
  if (it == module_definitions_.end()) {
    return nullptr;
  }
  return it->second;
}

bool MultiFileResolver::HasModuleDefinition(std::string_view module_name) const {
  return module_definitions_.count(std::string(module_name)) > 0;
}

std::vector<std::string> MultiFileResolver::GetAllModuleNames() const {
  std::vector<std::string> names;
  names.reserve(module_definitions_.size());
  for (const auto& [name, _] : module_definitions_) {
    names.push_back(name);
  }
  return names;
}

std::vector<ModuleInstance> MultiFileResolver::GetModuleInstances(
    std::string_view module_type) const {
  std::vector<ModuleInstance> result;
  for (const auto& inst : instances_) {
    if (inst.module_type == module_type) {
      result.push_back(inst);
    }
  }
  return result;
}

std::vector<ModuleInstance> MultiFileResolver::GetInstancesInModule(
    std::string_view parent_module) const {
  std::vector<ModuleInstance> result;
  for (const auto& inst : instances_) {
    if (inst.parent_module == parent_module) {
      result.push_back(inst);
    }
  }
  return result;
}

absl::Status MultiFileResolver::BuildDependencyGraph() {
  dependency_graph_ = DependencyGraph();
  BuildDependencyGraphInternal();
  return absl::OkStatus();
}

bool MultiFileResolver::HasCircularDependencies() const {
  return dependency_graph_.HasCycles();
}

std::vector<std::vector<std::string>> MultiFileResolver::GetCircularDependencies() const {
  return dependency_graph_.DetectCircularDependencies();
}

absl::Status MultiFileResolver::ValidateModuleReferences() {
  std::vector<std::string> undefined;
  
  for (const auto& inst : instances_) {
    if (!HasModuleDefinition(inst.module_type)) {
      undefined.push_back(inst.module_type);
    }
  }
  
  if (!undefined.empty()) {
    return absl::NotFoundError(
        absl::StrCat("Undefined modules: ", absl::StrJoin(undefined, ", ")));
  }
  
  return absl::OkStatus();
}

std::vector<std::string> MultiFileResolver::GetUndefinedModules() const {
  std::set<std::string> undefined_set;
  
  for (const auto& inst : instances_) {
    if (!HasModuleDefinition(inst.module_type)) {
      undefined_set.insert(inst.module_type);
    }
  }
  
  return std::vector<std::string>(undefined_set.begin(), undefined_set.end());
}

void MultiFileResolver::ExtractModuleDefinitions() {
  // TODO: Implement extraction from symbol table
  // This will iterate through the symbol table and find all module definitions
  // For now, this is a stub that does nothing
}

void MultiFileResolver::ExtractModuleInstances() {
  // TODO: Implement extraction from symbol table
  // This will iterate through the symbol table and find all module instances
  // For now, this is a stub that does nothing
}

void MultiFileResolver::BuildDependencyGraphInternal() {
  // Build graph from instances
  for (const auto& inst : instances_) {
    dependency_graph_.AddDependency(inst.parent_module, inst.module_type);
  }
}

}  // namespace analysis
}  // namespace verilog

