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

// JSON exporter for Verible semantic analysis results.
// Exports CallGraph, DataFlow, Unused entities, and Module hierarchy as JSON.

#ifndef VERIBLE_VERILOG_TOOLS_SEMANTIC_JSON_EXPORTER_H_
#define VERIBLE_VERILOG_TOOLS_SEMANTIC_JSON_EXPORTER_H_

#include <string>

namespace verilog {

// Forward declarations
class CallGraphEnhancer;

/**
 * @brief Exports Verible semantic analysis results to JSON format.
 *
 * This class provides methods to export various semantic analysis results
 * (call graphs, data flow, unused entities, module hierarchy) to JSON format
 * for consumption by external tools.
 */
class SemanticJsonExporter {
 public:
  SemanticJsonExporter() = default;

  /**
   * @brief Export call graph analysis to JSON.
   *
   * Exports function/task call graph including nodes (functions/tasks),
   * edges (call relationships), statistics, and recursion information.
   *
   * @param cg The CallGraphEnhancer containing the call graph data
   * @return JSON string representing the call graph
   */
  std::string ExportCallGraph(const CallGraphEnhancer& cg) const;

  /**
   * @brief Set whether to pretty-print JSON output.
   *
   * @param pretty If true, output formatted JSON with indentation
   */
  void SetPrettyPrint(bool pretty) { pretty_print_ = pretty; }

 private:
  bool pretty_print_ = true;  // Default to pretty-printed output
};

}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_SEMANTIC_JSON_EXPORTER_H_

