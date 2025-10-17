//Copyright 2017-2025 The Verible Authors.
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

#ifndef VERIBLE_VERILOG_ANALYSIS_ENHANCED_UNUSED_DETECTOR_H_
#define VERIBLE_VERILOG_ANALYSIS_ENHANCED_UNUSED_DETECTOR_H_

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "verible/common/text/symbol.h"
#include "verible/verilog/analysis/data-flow-analyzer.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {

// Represents an entity detected as unused
struct UnusedEntity {
  // Identity
  std::string name;                      // Entity name
  std::string fully_qualified_name;      // Full hierarchical name
  
  // Source information
  const verible::Symbol* syntax_origin;  // CST node where declared
  const VerilogSourceFile* file;         // Source file
  int line_number;                       // Line number
  
  // Entity type
  enum EntityType {
    kSignal,            // Wire, reg, logic
    kVariable,          // Local variable
    kFunction,          // Function
    kTask,              // Task
    kModule,            // Module definition
    kPort,              // Module port
    kParameter,         // Parameter
    kDeadCode           // Unreachable code block
  } type;
  
  // Reason for being unused
  enum UnusedReason {
    kNeverRead,         // Written but never read
    kNeverWritten,      // Read but never written (undriven)
    kNeverReferenced,   // Never referenced at all
    kUnreachable,       // Control flow never reaches
    kWriteOnly,         // Only written, never read
    kReadOnly           // Only read, never written
  } reason;
  
  // Additional context
  std::string explanation;               // Human-readable reason
  bool is_port;                          // Is this a port
  bool is_output;                        // Is this an output
  bool is_input;                         // Is this an input
  
  // Constructor
  UnusedEntity()
      : syntax_origin(nullptr),
        file(nullptr),
        line_number(0),
        type(kSignal),
        reason(kNeverReferenced),
        is_port(false),
        is_output(false),
        is_input(false) {}
};

// Tracks detailed usage statistics
struct UsageStatistics {
  // Counts
  int total_signals;
  int unused_signals;
  int write_only_signals;
  int read_only_signals;
  
  int total_variables;
  int unused_variables;
  
  int total_functions;
  int unused_functions;
  
  int total_tasks;
  int unused_tasks;
  
  int total_modules;
  int unused_modules;
  
  int dead_code_blocks;
  
  // Percentages
  float unused_signal_percentage;
  float unused_function_percentage;
  
  // Constructor
  UsageStatistics()
      : total_signals(0),
        unused_signals(0),
        write_only_signals(0),
        read_only_signals(0),
        total_variables(0),
        unused_variables(0),
        total_functions(0),
        unused_functions(0),
        total_tasks(0),
        unused_tasks(0),
        total_modules(0),
        unused_modules(0),
        dead_code_blocks(0),
        unused_signal_percentage(0.0f),
        unused_function_percentage(0.0f) {}
};

// Detects unused code entities using semantic data flow analysis
class EnhancedUnusedDetector {
 public:
  // Constructor
  EnhancedUnusedDetector(const DataFlowAnalyzer& dataflow_analyzer,
                         const SymbolTable& symbol_table);
  
  // Main analysis entry point
  absl::Status AnalyzeUnusedEntities();
  
  // Specific analysis methods
  absl::Status FindUnusedSignals();
  absl::Status FindWriteOnlySignals();
  absl::Status FindReadOnlySignals();
  absl::Status FindUnusedVariables();
  absl::Status FindUnusedFunctions();
  absl::Status FindUnusedTasks();
  absl::Status FindUnusedModules();
  absl::Status AnalyzeDeadCode();
  
  // Query methods
  std::vector<UnusedEntity> GetUnusedEntities() const { return unused_entities_; }
  std::vector<UnusedEntity> GetUnusedSignals() const;
  std::vector<UnusedEntity> GetUnusedFunctions() const;
  std::vector<UnusedEntity> GetWriteOnlySignals() const;
  std::vector<UnusedEntity> GetReadOnlySignals() const;
  UsageStatistics GetStatistics() const { return statistics_; }
  
  // Filtering and configuration
  void SetIgnorePorts(bool ignore) { ignore_ports_ = ignore; }
  void SetIgnoreOutputs(bool ignore) { ignore_outputs_ = ignore; }
  void SetIgnoreInputs(bool ignore) { ignore_inputs_ = ignore; }
  void AddIgnorePattern(const std::string& pattern);
  
  // Error/warning reporting
  std::vector<std::string> GetWarnings() const { return warnings_; }
  
 private:
  // Analysis helpers
  bool IsSignalUsed(const DataFlowNode& node);
  bool IsVariableUsed(const SymbolTableNode& node);
  bool IsFunctionCalled(const std::string& function_name);
  bool IsModuleInstantiated(const std::string& module_name);
  
  // Filtering helpers
  bool ShouldIgnore(const UnusedEntity& entity);
  bool MatchesIgnorePattern(const std::string& name);
  bool IsFalsePositive(const UnusedEntity& entity);
  
  // Port/direction detection
  bool IsPort(const DataFlowNode& node);
  bool IsOutput(const DataFlowNode& node);
  bool IsInput(const DataFlowNode& node);
  
  // Statistics computation
  void ComputeStatistics();
  void UpdateStatistics(const UnusedEntity& entity);
  
  // Warning reporting
  void AddWarning(const std::string& message, const verible::Symbol* origin);
  
  // Member variables
  const DataFlowAnalyzer& dataflow_analyzer_;
  const SymbolTable& symbol_table_;
  std::vector<UnusedEntity> unused_entities_;
  UsageStatistics statistics_;
  std::vector<std::string> warnings_;
  
  // Configuration
  bool ignore_ports_;
  bool ignore_outputs_;
  bool ignore_inputs_;
  std::vector<std::string> ignore_patterns_;
};

}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_ENHANCED_UNUSED_DETECTOR_H_

