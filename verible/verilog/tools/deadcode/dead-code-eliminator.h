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

#ifndef VERIBLE_VERILOG_TOOLS_DEADCODE_DEAD_CODE_ELIMINATOR_H_
#define VERIBLE_VERILOG_TOOLS_DEADCODE_DEAD_CODE_ELIMINATOR_H_

#include <set>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "verible/verilog/analysis/call-graph.h"

namespace verilog {
namespace tools {

// Report of dead code detection
struct DeadCodeReport {
  std::set<std::string> dead_functions;
  std::set<std::string> dead_tasks;
  std::set<std::string> dead_variables;
  int total_dead_count = 0;
  std::string summary;
};

// DeadCodeEliminator detects and removes unused code
class DeadCodeEliminator {
 public:
  // Construct with call graph for function/task analysis
  explicit DeadCodeEliminator(const verilog::analysis::CallGraph* call_graph);

  // Find all dead code (unreachable functions, tasks, unused variables)
  DeadCodeReport FindDeadCode();

  // Remove dead code safely
  // If dry_run is true, just reports what would be removed
  absl::Status Eliminate(const DeadCodeReport& report, bool dry_run = false);

 private:
  const verilog::analysis::CallGraph* call_graph_;
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_DEADCODE_DEAD_CODE_ELIMINATOR_H_

