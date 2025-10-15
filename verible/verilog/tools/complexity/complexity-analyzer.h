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

#ifndef VERIBLE_VERILOG_TOOLS_COMPLEXITY_COMPLEXITY_ANALYZER_H_
#define VERIBLE_VERILOG_TOOLS_COMPLEXITY_COMPLEXITY_ANALYZER_H_

#include <map>
#include <string>

#include "verible/verilog/analysis/call-graph.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-checker.h"

namespace verilog {
namespace tools {

// Report format options
enum class ReportFormat {
  kText,
  kJson,
  kHtml
};

// Complexity metrics for a single function/module
struct ComplexityMetrics {
  std::string name;
  int cyclomatic_complexity = 0;  // Number of decision points
  int call_depth = 0;              // Maximum call chain depth
  int function_size = 0;           // Lines of code
  int num_dependencies = 0;        // Number of functions called
  int fan_in = 0;                  // Number of callers
  int fan_out = 0;                 // Number of callees
};

// Overall project complexity report
struct ComplexityReport {
  std::map<std::string, ComplexityMetrics> per_function;
  int total_functions = 0;
  int average_complexity = 0;
  int max_complexity = 0;
  std::string most_complex_function;
};

// ComplexityAnalyzer provides code quality metrics
class ComplexityAnalyzer {
 public:
  // Construct with call graph, symbol table, and optional type checker
  explicit ComplexityAnalyzer(const verilog::analysis::CallGraph* call_graph,
                               const verilog::SymbolTable* symbol_table = nullptr,
                               const verilog::analysis::TypeChecker* type_checker = nullptr);

  // Analyze complexity for entire project
  ComplexityReport Analyze();

  // Generate report in specified format
  std::string GenerateReport(ReportFormat format);

  // Get metrics for specific function
  ComplexityMetrics GetFunctionMetrics(const std::string& function_name);

 private:
  const verilog::analysis::CallGraph* call_graph_;
  const verilog::SymbolTable* symbol_table_;
  const verilog::analysis::TypeChecker* type_checker_;
  ComplexityReport current_report_;
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_COMPLEXITY_COMPLEXITY_ANALYZER_H_

