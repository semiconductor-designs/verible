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

#include "verible/verilog/tools/semantic/json-exporter.h"

#include <string>

#include "nlohmann/json.hpp"
#include "verible/verilog/analysis/call-graph-enhancer.h"

namespace verilog {

std::string SemanticJsonExporter::ExportCallGraph(
    const CallGraphEnhancer& cg) const {
  nlohmann::json j;

  // Export nodes
  j["call_graph"]["nodes"] = nlohmann::json::array();
  for (const auto* node : cg.GetAllNodes()) {
    nlohmann::json node_json;
    node_json["name"] = node->name;
    // Convert NodeType enum to string
    node_json["type"] = (node->type == CallGraphNode::kTask) ? "task" : "function";
    node_json["call_depth"] = node->call_depth;
    node_json["is_entry_point"] = node->is_entry_point;
    node_json["is_recursive"] = node->is_recursive;
    node_json["is_unreachable"] = node->is_unreachable;
    node_json["caller_count"] = static_cast<int>(node->callers.size());
    node_json["callee_count"] = static_cast<int>(node->callees.size());
    j["call_graph"]["nodes"].push_back(node_json);
  }

  // Export edges
  j["call_graph"]["edges"] = nlohmann::json::array();
  for (const auto* edge : cg.GetAllEdges()) {
    nlohmann::json edge_json;
    edge_json["caller"] = edge->caller->name;
    edge_json["callee"] = edge->callee->name;
    j["call_graph"]["edges"].push_back(edge_json);
  }

  // Export statistics
  const auto& stats = cg.GetStatistics();
  j["call_graph"]["statistics"]["total_functions"] = stats.total_functions;
  j["call_graph"]["statistics"]["total_tasks"] = stats.total_tasks;
  j["call_graph"]["statistics"]["entry_points"] =
      static_cast<int>(cg.GetEntryPoints().size());
  j["call_graph"]["statistics"]["unreachable_functions"] =
      static_cast<int>(cg.GetUnreachableFunctions().size());
  j["call_graph"]["statistics"]["recursive_functions"] =
      stats.recursive_functions;
  j["call_graph"]["statistics"]["max_call_depth"] = stats.max_call_depth;

  // Export recursion cycles
  j["call_graph"]["recursion_cycles"] = nlohmann::json::array();
  for (const auto& cycle : cg.GetRecursionCycles()) {
    nlohmann::json cycle_json;
    cycle_json["cycle"] = nlohmann::json::array();
    for (const auto* node : cycle.cycle_nodes) {
      cycle_json["cycle"].push_back(node->name);
    }
    j["call_graph"]["recursion_cycles"].push_back(cycle_json);
  }

  // Return formatted JSON
  if (pretty_print_) {
    return j.dump(2);  // 2-space indent
  } else {
    return j.dump();
  }
}

}  // namespace verilog

