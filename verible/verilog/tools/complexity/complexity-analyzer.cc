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

#include "verible/verilog/tools/complexity/complexity-analyzer.h"

#include <map>
#include <string>

#include "absl/strings/str_cat.h"
#include "verible/verilog/analysis/call-graph.h"
#include "verible/verilog/analysis/type-checker.h"

namespace verilog {
namespace tools {

ComplexityAnalyzer::ComplexityAnalyzer(
    const verilog::analysis::CallGraph* call_graph,
    const verilog::analysis::TypeChecker* type_checker)
    : call_graph_(call_graph), type_checker_(type_checker) {}

ComplexityReport ComplexityAnalyzer::Analyze() {
  ComplexityReport report;
  
  if (!call_graph_) {
    return report;
  }
  
  // Get call graph metrics
  auto metrics = call_graph_->GetMetrics();
  report.total_functions = metrics.node_count;
  
  // For each node in call graph, compute metrics
  // TODO: Implement per-function analysis
  // For now, use aggregate metrics from call graph
  
  // Find most complex function (by call depth as proxy)
  if (metrics.max_call_depth > 0) {
    report.max_complexity = metrics.max_call_depth;
    // Would need to traverse call graph to find actual function
  }
  
  if (report.total_functions > 0) {
    report.average_complexity = metrics.max_call_depth / 2;  // Rough estimate
  }
  
  current_report_ = report;
  return report;
}

std::string ComplexityAnalyzer::GenerateReport(ReportFormat format) {
  std::string output;
  
  switch (format) {
    case ReportFormat::kText:
      output = absl::StrCat(
          "Complexity Analysis Report\n",
          "==========================\n\n",
          "Total Functions: ", current_report_.total_functions, "\n",
          "Average Complexity: ", current_report_.average_complexity, "\n",
          "Max Complexity: ", current_report_.max_complexity, "\n");
      if (!current_report_.most_complex_function.empty()) {
        output += absl::StrCat(
            "Most Complex: ", current_report_.most_complex_function, "\n");
      }
      break;
      
    case ReportFormat::kJson:
      output = absl::StrCat(
          "{\n",
          "  \"total_functions\": ", current_report_.total_functions, ",\n",
          "  \"average_complexity\": ", current_report_.average_complexity, ",\n",
          "  \"max_complexity\": ", current_report_.max_complexity, "\n",
          "}\n");
      break;
      
    case ReportFormat::kHtml:
      output = absl::StrCat(
          "<html><body>\n",
          "<h1>Complexity Analysis Report</h1>\n",
          "<table>\n",
          "<tr><td>Total Functions:</td><td>", current_report_.total_functions, "</td></tr>\n",
          "<tr><td>Average Complexity:</td><td>", current_report_.average_complexity, "</td></tr>\n",
          "<tr><td>Max Complexity:</td><td>", current_report_.max_complexity, "</td></tr>\n",
          "</table>\n",
          "</body></html>\n");
      break;
  }
  
  return output;
}

ComplexityMetrics ComplexityAnalyzer::GetFunctionMetrics(
    const std::string& function_name) {
  ComplexityMetrics metrics;
  metrics.name = function_name;
  
  // Check if function exists in report
  auto it = current_report_.per_function.find(function_name);
  if (it != current_report_.per_function.end()) {
    return it->second;
  }
  
  // Function not analyzed yet
  return metrics;
}

}  // namespace tools
}  // namespace verilog

