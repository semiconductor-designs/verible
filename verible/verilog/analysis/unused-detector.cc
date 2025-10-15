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

#include "verible/verilog/analysis/unused-detector.h"

#include <string>

namespace verilog {
namespace analysis {

UnusedDetector::UnusedDetector(const SymbolTable* symbol_table)
    : symbol_table_(symbol_table) {}

void UnusedDetector::Analyze() {
  unused_symbols_.clear();
  
  if (!symbol_table_) return;
  
  // Start analysis from the root scope
  AnalyzeScope(symbol_table_->Root());
}

void UnusedDetector::AnalyzeScope(const SymbolTableNode& scope) {
  // Check each symbol in this scope
  for (const auto& [name, child_node] : scope) {
    const SymbolInfo& info = child_node.Value();
    
    // Check if this symbol should be ignored
    if (ShouldIgnoreSymbol(info)) {
      continue;
    }
    
    // Check if this symbol is used
    if (!IsSymbolUsed(child_node)) {
      // Get file and line information
      std::string file_path = "unknown";  // TODO: Extract from info
      int line_number = 0;                // TODO: Extract from info
      
      unused_symbols_.emplace_back(
          std::string(name),
          file_path,
          line_number,
          GetSymbolType(info),
          GetScopeName(scope));
    }
    
    // Recursively analyze child scopes
    // Always try to analyze children (MapTree will handle empty case)
    AnalyzeScope(child_node);
  }
}

bool UnusedDetector::IsSymbolUsed(const SymbolTableNode& symbol) const {
  const SymbolInfo& info = symbol.Value();
  
  // Check if there are any references to bind
  // local_references_to_bind is a vector of DependentReferences
  const auto& refs = info.local_references_to_bind;
  
  // Simplified: A symbol is "used" if it has any references at all
  // Count non-empty references
  size_t ref_count = 0;
  for (const auto& ref : refs) {
    if (!ref.Empty() && ref.components) {
      ref_count++;
    }
  }
  
  // Symbol is "used" if it has at least min_references references
  return ref_count >= static_cast<size_t>(options_.min_references);
}

bool UnusedDetector::ShouldIgnoreSymbol(const SymbolInfo& info) const {
  // Ignore based on metatype
  const auto metatype = info.metatype;
  
  // Ignore parameters if configured
  if (options_.ignore_parameters) {
    if (metatype == SymbolMetaType::kParameter) {
      return true;
    }
  }
  
  // Ignore testbenches if configured
  // This would require checking if the symbol is in a testbench scope
  // For now, this is a placeholder
  if (options_.ignore_testbenches) {
    // TODO: Implement testbench detection
  }
  
  // Always ignore root-level imports and packages (they might be used externally)
  if (metatype == SymbolMetaType::kPackage) {
    return true;
  }
  
  return false;
}

std::string UnusedDetector::GetSymbolType(const SymbolInfo& info) const {
  switch (info.metatype) {
    case SymbolMetaType::kParameter:
      return "parameter";
    case SymbolMetaType::kTypeAlias:
      return "typedef";
    case SymbolMetaType::kModule:
      return "module";
    case SymbolMetaType::kClass:
      return "class";
    case SymbolMetaType::kFunction:
      return "function";
    case SymbolMetaType::kTask:
      return "task";
    case SymbolMetaType::kPackage:
      return "package";
    case SymbolMetaType::kDataNetVariableInstance:
      return "variable";
    default:
      return "symbol";
  }
}

std::string UnusedDetector::GetScopeName(const SymbolTableNode& scope) const {
  const SymbolInfo& info = scope.Value();
  
  // Try to get a meaningful scope name
  // For now, return the symbol type
  switch (info.metatype) {
    case SymbolMetaType::kModule:
      return "module";
    case SymbolMetaType::kClass:
      return "class";
    case SymbolMetaType::kFunction:
      return "function";
    case SymbolMetaType::kTask:
      return "task";
    case SymbolMetaType::kPackage:
      return "package";
    default:
      return "global";
  }
}

}  // namespace analysis
}  // namespace verilog

