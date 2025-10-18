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
#include "verible/verilog/analysis/kythe-analyzer.h"

namespace verilog {

namespace {
// Helper function to sanitize strings for JSON export
// Truncates very long strings to prevent memory issues
std::string SanitizeForJson(const std::string& str) {
  constexpr size_t kMaxStringLength = 10000;
  if (str.size() > kMaxStringLength) {
    return str.substr(0, kMaxStringLength) + "... [truncated]";
  }
  return str;
}
}  // namespace

std::string SemanticJsonExporter::ExportCallGraph(
    const CallGraphEnhancer& cg) const {
  nlohmann::json j;

  // Add schema versioning
  j["schema_version"] = "1.0.0";
  j["call_graph"]["version"] = "1.0.0";

  // Export nodes
  j["call_graph"]["nodes"] = nlohmann::json::array();
  for (const auto* node : cg.GetAllNodes()) {
    nlohmann::json node_json;
    node_json["name"] = SanitizeForJson(node->name);
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
    edge_json["caller"] = SanitizeForJson(edge->caller->name);
    edge_json["callee"] = SanitizeForJson(edge->callee->name);
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
      cycle_json["cycle"].push_back(SanitizeForJson(node->name));
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

  // Add schema versioning
  j["schema_version"] = "1.0.0";
  j["data_flow"]["version"] = "1.0.0";

  // Export nodes (from unordered_map)
  j["data_flow"]["nodes"] = nlohmann::json::array();
  for (const auto& [node_name, node] : graph.nodes) {
    nlohmann::json node_json;
    node_json["name"] = SanitizeForJson(node.name);
    node_json["local_name"] = SanitizeForJson(node.local_name);
    
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
      edge_json["source"] = SanitizeForJson(edge.source->name);
    }
    if (edge.target) {
      edge_json["target"] = SanitizeForJson(edge.target->name);
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
      param_json["name"] = SanitizeForJson(param->name);
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

  // Add schema versioning
  j["schema_version"] = "1.0.0";
  j["unused"]["version"] = "1.0.0";

  // Export unused entities
  j["unused"]["entities"] = nlohmann::json::array();
  for (const auto& entity : unused.GetUnusedEntities()) {
    nlohmann::json entity_json;
    entity_json["name"] = SanitizeForJson(entity.name);
    
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
    
    entity_json["fully_qualified_name"] = SanitizeForJson(entity.fully_qualified_name);
    
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

std::string SemanticJsonExporter::ExportKythe(
    const KytheAnalyzer& kythe) const {
  nlohmann::json j;

  // Add schema versioning (bump to 1.1.0 for Kythe support)
  j["schema_version"] = "1.1.0";
  j["kythe"]["version"] = "1.0.0";

  // Export variable references
  j["kythe"]["variable_references"] = nlohmann::json::array();
  for (const auto& ref : kythe.GetVariableReferences()) {
    nlohmann::json ref_json;
    ref_json["variable_name"] = SanitizeForJson(ref.variable_name);
    ref_json["fully_qualified_name"] = SanitizeForJson(ref.fully_qualified_name);
    
    // Export location
    nlohmann::json loc_json;
    loc_json["file"] = SanitizeForJson(ref.location.file_path);
    loc_json["byte_start"] = ref.location.byte_start;
    loc_json["byte_end"] = ref.location.byte_end;
    loc_json["line"] = ref.location.line;
    loc_json["column"] = ref.location.column;
    ref_json["location"] = loc_json;
    
    // Export reference type
    ref_json["type"] = KytheReferenceTypeToString(ref.type);
    
    // Export context information
    ref_json["parent_scope"] = SanitizeForJson(ref.parent_scope);
    if (!ref.context.empty()) {
      ref_json["context"] = SanitizeForJson(ref.context);
    }
    
    j["kythe"]["variable_references"].push_back(ref_json);
  }

  // Export variable definitions
  j["kythe"]["variable_definitions"] = nlohmann::json::array();
  for (const auto& def : kythe.GetVariableDefinitions()) {
    nlohmann::json def_json;
    def_json["variable_name"] = SanitizeForJson(def.variable_name);
    def_json["fully_qualified_name"] = SanitizeForJson(def.fully_qualified_name);
    
    // Export location
    nlohmann::json loc_json;
    loc_json["file"] = SanitizeForJson(def.location.file_path);
    loc_json["byte_start"] = def.location.byte_start;
    loc_json["byte_end"] = def.location.byte_end;
    loc_json["line"] = def.location.line;
    loc_json["column"] = def.location.column;
    def_json["location"] = loc_json;
    
    // Export variable kind
    def_json["kind"] = VariableKindToString(def.kind);
    
    j["kythe"]["variable_definitions"].push_back(def_json);
  }

  // Export statistics
  const auto& stats = kythe.GetStatistics();
  j["kythe"]["statistics"]["files_analyzed"] = stats.files_analyzed;
  j["kythe"]["statistics"]["total_facts"] = stats.total_facts;
  j["kythe"]["statistics"]["total_edges"] = stats.total_edges;
  j["kythe"]["statistics"]["total_references"] = stats.total_references;
  j["kythe"]["statistics"]["total_definitions"] = stats.total_definitions;
  j["kythe"]["statistics"]["read_references"] = stats.read_references;
  j["kythe"]["statistics"]["write_references"] = stats.write_references;
  j["kythe"]["statistics"]["read_write_references"] = stats.read_write_references;
  j["kythe"]["statistics"]["analysis_time_ms"] = stats.analysis_time_ms;

  // Return formatted JSON
  if (pretty_print_) {
    return j.dump(2);  // 2-space indent
  } else {
    return j.dump();
  }
}

}  // namespace verilog

