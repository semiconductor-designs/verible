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

#include "verible/verilog/analysis/enhanced-unused-detector.h"

#include <algorithm>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "verible/common/text/symbol.h"
#include "verible/verilog/analysis/data-flow-analyzer.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {

// EnhancedUnusedDetector implementation

EnhancedUnusedDetector::EnhancedUnusedDetector(
    const DataFlowAnalyzer& dataflow_analyzer,
    const SymbolTable& symbol_table)
    : dataflow_analyzer_(dataflow_analyzer),
      symbol_table_(symbol_table),
      ignore_ports_(false),
      ignore_outputs_(false),
      ignore_inputs_(false),
      use_regex_(false) {
  // symbol_table_ will be used for function/module analysis in future iterations
  (void)symbol_table_;
  
  // Initialize ignore patterns with common patterns
  ignore_patterns_.push_back("unused_");
  ignore_patterns_.push_back("_debug");
  ignore_patterns_.push_back("_reserved");
}

absl::Status EnhancedUnusedDetector::AnalyzeUnusedEntities() {
  // Clear previous results
  unused_entities_.clear();
  warnings_.clear();
  
  // Run all analyses
  auto status = FindUnusedSignals();
  if (!status.ok()) return status;
  
  status = FindWriteOnlySignals();
  if (!status.ok()) return status;
  
  status = FindReadOnlySignals();
  if (!status.ok()) return status;
  
  status = FindUnusedVariables();
  if (!status.ok()) return status;
  
  status = FindUnusedFunctions();
  if (!status.ok()) return status;
  
  status = FindUnusedTasks();
  if (!status.ok()) return status;
  
  status = FindUnusedModules();
  if (!status.ok()) return status;
  
  status = AnalyzeDeadCode();
  if (!status.ok()) return status;
  
  // Compute statistics
  ComputeStatistics();
  
  return absl::OkStatus();
}

absl::Status EnhancedUnusedDetector::FindUnusedSignals() {
  const auto& graph = dataflow_analyzer_.GetDataFlowGraph();
  
  // Iterate through all signals
  for (const auto* signal : graph.signals) {
    if (!signal) continue;
    
    // Check if signal is never read AND never written
    if (!signal->is_read && !signal->is_written) {
      UnusedEntity entity;
      entity.name = signal->local_name;
      entity.fully_qualified_name = signal->name;
      entity.type = UnusedEntity::kSignal;
      entity.reason = UnusedEntity::kNeverReferenced;
      entity.syntax_origin = signal->syntax_origin;
      entity.file = signal->file;
      entity.line_number = signal->line_number;
      entity.explanation = absl::StrCat("Signal '", signal->name, 
                                        "' is never read or written");
      entity.is_port = signal->is_port;
      
      // Filter if should be ignored
      if (!ShouldIgnore(entity)) {
        unused_entities_.push_back(entity);
        statistics_.unused_signals++;
      }
    }
    
    statistics_.total_signals++;
  }
  
  return absl::OkStatus();
}

absl::Status EnhancedUnusedDetector::FindWriteOnlySignals() {
  const auto& graph = dataflow_analyzer_.GetDataFlowGraph();
  
  // Iterate through all signals
  for (const auto* signal : graph.signals) {
    if (!signal) continue;
    
    // Check if signal is written but never read
    if (signal->is_written && !signal->is_read) {
      UnusedEntity entity;
      entity.name = signal->local_name;
      entity.fully_qualified_name = signal->name;
      entity.type = UnusedEntity::kSignal;
      entity.reason = UnusedEntity::kWriteOnly;
      entity.syntax_origin = signal->syntax_origin;
      entity.file = signal->file;
      entity.line_number = signal->line_number;
      entity.explanation = absl::StrCat("Signal '", signal->name, 
                                        "' is written but never read");
      entity.is_port = signal->is_port;
      entity.is_output = IsOutput(*signal);
      
      // Filter if should be ignored
      if (!ShouldIgnore(entity)) {
        unused_entities_.push_back(entity);
        statistics_.write_only_signals++;
      }
    }
  }
  
  return absl::OkStatus();
}

absl::Status EnhancedUnusedDetector::FindReadOnlySignals() {
  const auto& graph = dataflow_analyzer_.GetDataFlowGraph();
  
  // Iterate through all signals
  for (const auto* signal : graph.signals) {
    if (!signal) continue;
    
    // Check if signal is read but never written (undriven)
    if (signal->is_read && !signal->is_written) {
      UnusedEntity entity;
      entity.name = signal->local_name;
      entity.fully_qualified_name = signal->name;
      entity.type = UnusedEntity::kSignal;
      entity.reason = UnusedEntity::kReadOnly;
      entity.syntax_origin = signal->syntax_origin;
      entity.file = signal->file;
      entity.line_number = signal->line_number;
      entity.explanation = absl::StrCat("Signal '", signal->name, 
                                        "' is read but never written (undriven)");
      entity.is_port = signal->is_port;
      entity.is_input = IsInput(*signal);
      
      // Filter if should be ignored
      if (!ShouldIgnore(entity)) {
        unused_entities_.push_back(entity);
        statistics_.read_only_signals++;
      }
    }
  }
  
  return absl::OkStatus();
}

absl::Status EnhancedUnusedDetector::FindUnusedVariables() {
  const auto& graph = dataflow_analyzer_.GetDataFlowGraph();
  
  // Iterate through all variables
  for (const auto* variable : graph.variables) {
    if (!variable) continue;
    
    // Check if variable is never read AND never written
    if (!variable->is_read && !variable->is_written) {
      UnusedEntity entity;
      entity.name = variable->local_name;
      entity.fully_qualified_name = variable->name;
      entity.type = UnusedEntity::kVariable;
      entity.reason = UnusedEntity::kNeverReferenced;
      entity.syntax_origin = variable->syntax_origin;
      entity.file = variable->file;
      entity.line_number = variable->line_number;
      entity.explanation = absl::StrCat("Variable '", variable->name, 
                                        "' is never referenced");
      
      // Filter if should be ignored
      if (!ShouldIgnore(entity)) {
        unused_entities_.push_back(entity);
        statistics_.unused_variables++;
      }
    }
    
    statistics_.total_variables++;
  }
  
  return absl::OkStatus();
}

absl::Status EnhancedUnusedDetector::FindUnusedFunctions() {
  // TODO: Implement function call detection
  // This requires traversing the symbol table for kFunction metatype
  // and searching for call sites
  // For now, return OK (stub)
  return absl::OkStatus();
}

absl::Status EnhancedUnusedDetector::FindUnusedTasks() {
  // TODO: Implement task call detection
  // Similar to FindUnusedFunctions but for tasks
  // For now, return OK (stub)
  return absl::OkStatus();
}

absl::Status EnhancedUnusedDetector::FindUnusedModules() {
  // TODO: Implement module instantiation detection
  // Traverse symbol table for module definitions
  // Search for module instances
  // For now, return OK (stub)
  return absl::OkStatus();
}

absl::Status EnhancedUnusedDetector::AnalyzeDeadCode() {
  // TODO: Implement dead code detection
  // Analyze constant conditions in if/case statements
  // For now, return OK (stub)
  return absl::OkStatus();
}

// Query methods

std::vector<UnusedEntity> EnhancedUnusedDetector::GetUnusedSignals() const {
  std::vector<UnusedEntity> signals;
  for (const auto& entity : unused_entities_) {
    if (entity.type == UnusedEntity::kSignal &&
        entity.reason == UnusedEntity::kNeverReferenced) {
      signals.push_back(entity);
    }
  }
  return signals;
}

std::vector<UnusedEntity> EnhancedUnusedDetector::GetUnusedFunctions() const {
  std::vector<UnusedEntity> functions;
  for (const auto& entity : unused_entities_) {
    if (entity.type == UnusedEntity::kFunction ||
        entity.type == UnusedEntity::kTask) {
      functions.push_back(entity);
    }
  }
  return functions;
}

std::vector<UnusedEntity> EnhancedUnusedDetector::GetWriteOnlySignals() const {
  std::vector<UnusedEntity> signals;
  for (const auto& entity : unused_entities_) {
    if (entity.type == UnusedEntity::kSignal &&
        entity.reason == UnusedEntity::kWriteOnly) {
      signals.push_back(entity);
    }
  }
  return signals;
}

std::vector<UnusedEntity> EnhancedUnusedDetector::GetReadOnlySignals() const {
  std::vector<UnusedEntity> signals;
  for (const auto& entity : unused_entities_) {
    if (entity.type == UnusedEntity::kSignal &&
        entity.reason == UnusedEntity::kReadOnly) {
      signals.push_back(entity);
    }
  }
  return signals;
}

// Configuration methods

void EnhancedUnusedDetector::AddIgnorePattern(const std::string& pattern) {
  ignore_patterns_.push_back(pattern);
  
  // If regex mode enabled, compile the pattern
  if (use_regex_) {
    try {
      compiled_regex_.emplace_back(pattern);
    } catch (const std::regex_error& e) {
      // Log warning if regex is invalid
      AddWarning(absl::StrCat("Invalid regex pattern: ", pattern, " - ", e.what()), nullptr);
    }
  }
}

// Helper methods

bool EnhancedUnusedDetector::IsSignalUsed(const DataFlowNode& node) {
  return node.is_read || node.is_written;
}

bool EnhancedUnusedDetector::IsVariableUsed(const SymbolTableNode& node) {
  // Check if variable appears in data flow graph
  // If it does, check if it's used
  // For now, return false (stub)
  (void)node;
  return false;
}

bool EnhancedUnusedDetector::IsFunctionCalled(const std::string& function_name) {
  // TODO: Search for function calls in symbol table
  // For now, return false (stub)
  (void)function_name;
  return false;
}

bool EnhancedUnusedDetector::IsModuleInstantiated(const std::string& module_name) {
  // TODO: Search for module instances in symbol table
  // For now, return false (stub)
  (void)module_name;
  return false;
}

bool EnhancedUnusedDetector::ShouldIgnore(const UnusedEntity& entity) {
  // Apply filtering rules
  
  // 1. Check if it's a false positive
  if (IsFalsePositive(entity)) {
    return true;
  }
  
  // 2. Check ignore patterns
  if (MatchesIgnorePattern(entity.name)) {
    return true;
  }
  
  // 3. Check port ignoring rules
  if (ignore_ports_ && entity.is_port) {
    return true;
  }
  
  // 4. Check output ignoring (write-only outputs are OK)
  if (ignore_outputs_ && entity.is_output && 
      entity.reason == UnusedEntity::kWriteOnly) {
    return true;
  }
  
  // 5. Check input ignoring (read-only inputs are OK)
  if (ignore_inputs_ && entity.is_input && 
      entity.reason == UnusedEntity::kReadOnly) {
    return true;
  }
  
  return false;
}

bool EnhancedUnusedDetector::MatchesIgnorePattern(const std::string& name) {
  if (use_regex_) {
    // Use compiled regex patterns
    for (const auto& regex : compiled_regex_) {
      if (std::regex_search(name, regex)) {
        return true;
      }
    }
  } else {
    // Use simple substring matching (backward compatible)
    for (const auto& pattern : ignore_patterns_) {
      if (name.find(pattern) != std::string::npos) {
        return true;
      }
    }
  }
  return false;
}

bool EnhancedUnusedDetector::IsFalsePositive(const UnusedEntity& entity) {
  // Check for common false positive patterns
  
  // Signals starting with "unused_" are intentionally unused
  if (absl::StartsWith(entity.name, "unused_")) {
    return true;
  }
  
  // Debug signals
  if (entity.name.find("debug") != std::string::npos) {
    return true;
  }
  
  // Reserved for future
  if (entity.name.find("reserved") != std::string::npos) {
    return true;
  }
  
  return false;
}

bool EnhancedUnusedDetector::IsPort(const DataFlowNode& node) {
  return node.is_port;
}

bool EnhancedUnusedDetector::IsOutput(const DataFlowNode& node) {
  // TODO: Check port direction from CST
  // For now, assume write-only ports are outputs
  return node.is_port && node.is_written && !node.is_read;
}

bool EnhancedUnusedDetector::IsInput(const DataFlowNode& node) {
  // TODO: Check port direction from CST
  // For now, assume read-only ports are inputs
  return node.is_port && node.is_read && !node.is_written;
}

void EnhancedUnusedDetector::ComputeStatistics() {
  // Compute percentages
  if (statistics_.total_signals > 0) {
    statistics_.unused_signal_percentage = 
        (float)statistics_.unused_signals / statistics_.total_signals * 100.0f;
  }
  
  if (statistics_.total_functions > 0) {
    statistics_.unused_function_percentage = 
        (float)statistics_.unused_functions / statistics_.total_functions * 100.0f;
  }
}

void EnhancedUnusedDetector::UpdateStatistics(const UnusedEntity& entity) {
  switch (entity.type) {
    case UnusedEntity::kSignal:
      statistics_.unused_signals++;
      break;
    case UnusedEntity::kVariable:
      statistics_.unused_variables++;
      break;
    case UnusedEntity::kFunction:
      statistics_.unused_functions++;
      break;
    case UnusedEntity::kTask:
      statistics_.unused_tasks++;
      break;
    case UnusedEntity::kModule:
      statistics_.unused_modules++;
      break;
    case UnusedEntity::kDeadCode:
      statistics_.dead_code_blocks++;
      break;
    default:
      break;
  }
}

void EnhancedUnusedDetector::AddWarning(const std::string& message,
                                        const verible::Symbol* origin) {
  // TODO: Add file and line number information from origin
  (void)origin;
  warnings_.push_back(message);
}

}  // namespace verilog

