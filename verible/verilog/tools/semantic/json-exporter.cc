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
#include "verible/verilog/analysis/data-flow-analyzer.h"
#include "verible/verilog/analysis/enhanced-unused-detector.h"

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

std::string SemanticJsonExporter::ExportDataFlow(
    const DataFlowAnalyzer& df) const {
  nlohmann::json j;
  const auto& graph = df.GetDataFlowGraph();

  // Export nodes (from unordered_map)
  j["data_flow"]["nodes"] = nlohmann::json::array();
  for (const auto& [node_name, node] : graph.nodes) {
    nlohmann::json node_json;
    node_json["name"] = node.name;
    node_json["local_name"] = node.local_name;
    
    // Node type
    std::string type_str;
    switch (node.type) {
      case DataFlowNode::kSignal:
        type_str = "signal";
        break;
      case DataFlowNode::kVariable:
        type_str = "variable";
        break;
      case DataFlowNode::kPort:
        type_str = "port";
        break;
      case DataFlowNode::kParameter:
        type_str = "parameter";
        break;
      case DataFlowNode::kConstant:
        type_str = "constant";
        break;
      default:
        type_str = "unknown";
    }
    node_json["type"] = type_str;
    
    // Flags
    node_json["is_constant"] = node.is_constant;
    node_json["is_parameter"] = node.is_parameter;
    node_json["is_port"] = node.is_port;
    node_json["is_read"] = node.is_read;
    node_json["is_written"] = node.is_written;
    node_json["has_multi_driver"] = node.has_multi_driver;
    node_json["fanout"] = node.fanout;
    node_json["driver_count"] = node.driver_count;
    
    j["data_flow"]["nodes"].push_back(node_json);
  }

  // Export edges
  j["data_flow"]["edges"] = nlohmann::json::array();
  for (const auto& edge : graph.edges) {
    nlohmann::json edge_json;
    // Export node names (pointers need to be converted)
    if (edge.source) {
      edge_json["source"] = edge.source->name;
    }
    if (edge.target) {
      edge_json["target"] = edge.target->name;
    }
    
    // Edge type
    std::string edge_type_str;
    switch (edge.type) {
      case DataFlowEdge::kBlocking:
        edge_type_str = "blocking";
        break;
      case DataFlowEdge::kNonBlocking:
        edge_type_str = "non_blocking";
        break;
      case DataFlowEdge::kContinuous:
        edge_type_str = "continuous";
        break;
      case DataFlowEdge::kPortConnection:
        edge_type_str = "port_connection";
        break;
      case DataFlowEdge::kFunctionReturn:
        edge_type_str = "function_return";
        break;
      case DataFlowEdge::kFunctionArg:
        edge_type_str = "function_arg";
        break;
      default:
        edge_type_str = "unknown";
    }
    edge_json["type"] = edge_type_str;
    edge_json["is_conditional"] = edge.is_conditional;
    
    j["data_flow"]["edges"].push_back(edge_json);
  }

  // Export parameters
  j["data_flow"]["parameters"] = nlohmann::json::array();
  for (const auto* param : graph.parameters) {
    if (param) {
      nlohmann::json param_json;
      param_json["name"] = param->name;
      param_json["is_constant"] = param->is_constant;
      j["data_flow"]["parameters"].push_back(param_json);
    }
  }

  // Export constant list
  j["data_flow"]["constant_list"] = graph.constant_list;

  // Return formatted JSON
  if (pretty_print_) {
    return j.dump(2);
  } else {
    return j.dump();
  }
}

std::string SemanticJsonExporter::ExportUnused(
    const EnhancedUnusedDetector& unused) const {
  nlohmann::json j;

  // Export unused entities
  j["unused"]["entities"] = nlohmann::json::array();
  for (const auto& entity : unused.GetUnusedEntities()) {
    nlohmann::json entity_json;
    entity_json["name"] = entity.name;
    
    // Entity type
    std::string type_str;
    switch (entity.type) {
      case UnusedEntity::kSignal:
        type_str = "signal";
        break;
      case UnusedEntity::kVariable:
        type_str = "variable";
        break;
      case UnusedEntity::kFunction:
        type_str = "function";
        break;
      case UnusedEntity::kTask:
        type_str = "task";
        break;
      case UnusedEntity::kModule:
        type_str = "module";
        break;
      case UnusedEntity::kPort:
        type_str = "port";
        break;
      case UnusedEntity::kParameter:
        type_str = "parameter";
        break;
      case UnusedEntity::kDeadCode:
        type_str = "dead_code";
        break;
      default:
        type_str = "unknown";
    }
    entity_json["type"] = type_str;
    
    entity_json["fully_qualified_name"] = entity.fully_qualified_name;
    
    j["unused"]["entities"].push_back(entity_json);
  }

  // Export statistics
  const auto& stats = unused.GetStatistics();
  j["unused"]["statistics"]["total_signals"] = stats.total_signals;
  j["unused"]["statistics"]["unused_signals"] = stats.unused_signals;
  j["unused"]["statistics"]["total_variables"] = stats.total_variables;
  j["unused"]["statistics"]["unused_variables"] = stats.unused_variables;
  j["unused"]["statistics"]["total_functions"] = stats.total_functions;
  j["unused"]["statistics"]["unused_functions"] = stats.unused_functions;
  j["unused"]["statistics"]["total_modules"] = stats.total_modules;
  j["unused"]["statistics"]["unused_modules"] = stats.unused_modules;

  // Summary
  int total_unused = stats.unused_signals + stats.unused_variables +
                     stats.unused_functions + stats.unused_modules;
  j["unused"]["summary"] = std::to_string(total_unused) + " unused entities detected";

  // Return formatted JSON
  if (pretty_print_) {
    return j.dump(2);
  } else {
    return j.dump();
  }
}

}  // namespace verilog

