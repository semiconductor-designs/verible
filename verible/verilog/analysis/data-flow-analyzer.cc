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

#include "verible/verilog/analysis/data-flow-analyzer.h"

#include <algorithm>
#include <queue>
#include <string>
#include <unordered_set>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "verible/common/analysis/syntax-tree-search.h"
#include "verible/common/text/concrete-syntax-leaf.h"
#include "verible/common/text/concrete-syntax-tree.h"
#include "verible/common/text/symbol.h"
#include "verible/common/text/token-info.h"
#include "verible/common/text/tree-utils.h"
#include "verible/verilog/CST/verilog-matchers.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {

// DataFlowGraph method implementations

DataFlowNode* DataFlowGraph::FindNode(const std::string& name) {
  auto it = nodes.find(name);
  if (it != nodes.end()) {
    return &it->second;
  }
  return nullptr;
}

void DataFlowGraph::AddEdge(DataFlowNode* source, DataFlowNode* target,
                            DataFlowEdge::EdgeType type) {
  if (!source || !target) return;
  
  DataFlowEdge edge;
  edge.source = source;
  edge.target = target;
  edge.type = type;
  
  edges.push_back(edge);
  
  // Update node relationships
  source->outgoing_edges.push_back(&edges.back());
  target->incoming_edges.push_back(&edges.back());
}

std::vector<DataFlowNode*> DataFlowGraph::GetDriversOf(const std::string& name) {
  DataFlowNode* node = FindNode(name);
  if (!node) return {};
  return node->drivers;
}

std::vector<DataFlowNode*> DataFlowGraph::GetReadersOf(const std::string& name) {
  DataFlowNode* node = FindNode(name);
  if (!node) return {};
  return node->readers;
}

std::vector<std::string> DataFlowGraph::GetDependencyChain(const std::string& name) {
  auto it = dependencies.find(name);
  if (it != dependencies.end()) {
    return it->second;
  }
  return {};
}

bool DataFlowGraph::HasMultiDriver(const std::string& name) {
  DataFlowNode* node = FindNode(name);
  if (!node) return false;
  return node->has_multi_driver;
}

// DataFlowAnalyzer method implementations

DataFlowAnalyzer::DataFlowAnalyzer(const SymbolTable& symbol_table,
                                   const VerilogProject& project)
    : symbol_table_(symbol_table), project_(project) {
  // project_ will be used for error reporting in future iterations
  (void)project_;
}

absl::Status DataFlowAnalyzer::AnalyzeDataFlow() {
  // Build the complete data flow graph
  auto status = BuildDataFlowGraph();
  if (!status.ok()) return status;
  
  // Perform analyses
  status = DetectMultiDrivers();
  if (!status.ok()) return status;
  
  status = AnalyzeDependencies();
  if (!status.ok()) return status;
  
  status = PropagateConstants();
  if (!status.ok()) return status;
  
  status = AnalyzePortDataFlow();
  if (!status.ok()) return status;
  
  return absl::OkStatus();
}

absl::Status DataFlowAnalyzer::BuildDataFlowGraph() {
  // Traverse the symbol table to extract all nodes
  TraverseSymbolTable(symbol_table_.Root(), "");
  
  // Extract all assignments to build edges
  ExtractAssignments(symbol_table_.Root());
  
  // Analyze drivers and readers
  AnalyzeDrivers();
  AnalyzeReaders();
  ComputeFanout();
  
  return absl::OkStatus();
}

void DataFlowAnalyzer::TraverseSymbolTable(const SymbolTableNode& node,
                                           const std::string& scope) {
  // Extract different types of nodes
  ExtractSignals(node, scope);
  ExtractVariables(node, scope);
  ExtractPorts(node, scope);
  ExtractParameters(node, scope);
  
  // Recurse to children
  std::string current_scope = scope.empty() ? 
      std::string(*node.Key()) : absl::StrCat(scope, ".", *node.Key());
  
  for (const auto& child : node.Children()) {
    TraverseSymbolTable(child.second, current_scope);
  }
}

void DataFlowAnalyzer::ExtractSignals(const SymbolTableNode& node,
                                      const std::string& scope) {
  const auto& info = node.Value();
  
  // Check if this is a signal (wire, reg, logic)
  if (info.metatype == SymbolMetaType::kDataNetVariableInstance) {
    DataFlowNode df_node;
    df_node.name = scope.empty() ? 
        std::string(*node.Key()) : absl::StrCat(scope, ".", *node.Key());
    df_node.local_name = std::string(*node.Key());
    df_node.type = DataFlowNode::kSignal;
    df_node.syntax_origin = info.syntax_origin;
    df_node.file = info.file_origin;
    df_node.scope = scope;
    df_node.symbol_node = &node;
    
    // Store in graph
    graph_.nodes[df_node.name] = df_node;
    graph_.signals.push_back(&graph_.nodes[df_node.name]);
  }
}

void DataFlowAnalyzer::ExtractVariables(const SymbolTableNode& node,
                                        const std::string& scope) {
  // Variables are local to functions/tasks
  // For now, treat them similar to signals but mark as variables
  const auto& info = node.Value();
  
  if (info.metatype == SymbolMetaType::kDataNetVariableInstance) {
    // Check if we're inside a function or task scope
    if (scope.find("function") != std::string::npos ||
        scope.find("task") != std::string::npos) {
      DataFlowNode df_node;
      df_node.name = scope.empty() ? 
          std::string(*node.Key()) : absl::StrCat(scope, ".", *node.Key());
      df_node.local_name = std::string(*node.Key());
      df_node.type = DataFlowNode::kVariable;
      df_node.syntax_origin = info.syntax_origin;
      df_node.file = info.file_origin;
      df_node.scope = scope;
      df_node.symbol_node = &node;
      
      graph_.nodes[df_node.name] = df_node;
      graph_.variables.push_back(&graph_.nodes[df_node.name]);
    }
  }
}

void DataFlowAnalyzer::ExtractPorts(const SymbolTableNode& node,
                                    const std::string& scope) {
  // Ports are typically represented as kDataNetVariableInstance with special flags
  // For now, we'll skip dedicated port extraction and handle ports as signals
  // TODO: Enhance port detection logic
  (void)node;
  (void)scope;
}

void DataFlowAnalyzer::ExtractParameters(const SymbolTableNode& node,
                                         const std::string& scope) {
  const auto& info = node.Value();
  
  // Check if this is a parameter
  if (info.metatype == SymbolMetaType::kParameter) {
    DataFlowNode df_node;
    df_node.name = scope.empty() ? 
        std::string(*node.Key()) : absl::StrCat(scope, ".", *node.Key());
    df_node.local_name = std::string(*node.Key());
    df_node.type = DataFlowNode::kParameter;
    df_node.is_parameter = true;
    df_node.is_constant = true;  // Parameters are always constants
    df_node.syntax_origin = info.syntax_origin;
    df_node.file = info.file_origin;
    df_node.scope = scope;
    df_node.symbol_node = &node;
    
    graph_.nodes[df_node.name] = df_node;
    graph_.parameters.push_back(&graph_.nodes[df_node.name]);
    graph_.constant_list.push_back(df_node.name);
  }
}

void DataFlowAnalyzer::ExtractAssignments(const SymbolTableNode& node) {
  // For now, stub implementation
  // Will extract assignments from CST in next iteration
  
  // TODO: Implement assignment extraction
  // - Extract blocking assignments (=)
  // - Extract non-blocking assignments (<=)
  // - Extract continuous assignments (assign)
  // - Extract port connections
}

void DataFlowAnalyzer::ExtractBlockingAssignments(const verible::Symbol& syntax) {
  // TODO: Implement blocking assignment extraction
}

void DataFlowAnalyzer::ExtractNonBlockingAssignments(const verible::Symbol& syntax) {
  // TODO: Implement non-blocking assignment extraction
}

void DataFlowAnalyzer::ExtractContinuousAssignments(const verible::Symbol& syntax) {
  // TODO: Implement continuous assignment extraction
}

void DataFlowAnalyzer::ExtractPortConnections(const verible::Symbol& syntax) {
  // TODO: Implement port connection extraction
}

void DataFlowAnalyzer::AnalyzeDrivers() {
  // Analyze driver relationships from edges
  for (auto& edge : graph_.edges) {
    if (edge.source && edge.target) {
      // Add source as a driver of target
      edge.target->drivers.push_back(edge.source);
      edge.target->driver_count++;
      edge.target->is_written = true;
    }
  }
}

void DataFlowAnalyzer::AnalyzeReaders() {
  // Analyze reader relationships from edges
  for (auto& edge : graph_.edges) {
    if (edge.source && edge.target) {
      // Add target as a reader of source
      edge.source->readers.push_back(edge.target);
      edge.source->is_read = true;
    }
  }
}

void DataFlowAnalyzer::ComputeFanout() {
  // Compute fanout for each node
  for (auto& pair : graph_.nodes) {
    pair.second.fanout = pair.second.readers.size();
  }
}

std::vector<DataFlowNode*> DataFlowAnalyzer::GetDriversOf(
    const std::string& signal_name) {
  return graph_.GetDriversOf(signal_name);
}

std::vector<DataFlowNode*> DataFlowAnalyzer::GetReadersOf(
    const std::string& signal_name) {
  return graph_.GetReadersOf(signal_name);
}

std::vector<std::string> DataFlowAnalyzer::GetDependencyChain(
    const std::string& signal_name) {
  return graph_.GetDependencyChain(signal_name);
}

absl::Status DataFlowAnalyzer::DetectMultiDrivers() {
  // Check for multi-driver conflicts
  CheckMultiDriverConflicts();
  return absl::OkStatus();
}

void DataFlowAnalyzer::CheckMultiDriverConflicts() {
  for (auto& pair : graph_.nodes) {
    auto& node = pair.second;
    
    if (node.driver_count > 1) {
      // Check if this is a valid multi-driver scenario
      if (!IsValidMultiDriver(node)) {
        node.has_multi_driver = true;
        graph_.multi_driver_nodes.push_back(&node);
        
        AddError(absl::StrCat("Multi-driver conflict on signal '", 
                             node.name, "' (", node.driver_count, " drivers)"),
                node.syntax_origin);
      }
    }
  }
}

bool DataFlowAnalyzer::IsValidMultiDriver(const DataFlowNode& node) {
  // Valid multi-driver scenarios:
  // 1. Inout ports (bidirectional)
  // 2. Tri-state logic with high-impedance
  
  // Check if it's an inout port
  if (node.is_port) {
    // TODO: Check port direction from CST
    // For now, assume inout ports are valid
    return true;
  }
  
  return false;
}

absl::Status DataFlowAnalyzer::AnalyzeDependencies() {
  // Build dependency chains
  BuildDependencyChains();
  return absl::OkStatus();
}

void DataFlowAnalyzer::BuildDependencyChains() {
  // For each node, compute its transitive dependencies
  for (const auto& pair : graph_.nodes) {
    const std::string& node_name = pair.first;
    graph_.dependencies[node_name] = ComputeTransitiveClosure(node_name);
  }
}

std::vector<std::string> DataFlowAnalyzer::ComputeTransitiveClosure(
    const std::string& node_name) {
  std::vector<std::string> result;
  std::unordered_set<std::string> visited;
  std::queue<std::string> queue;
  
  queue.push(node_name);
  
  while (!queue.empty()) {
    std::string current = queue.front();
    queue.pop();
    
    if (visited.find(current) != visited.end()) {
      continue;
    }
    
    visited.insert(current);
    result.push_back(current);
    
    // Get drivers of current node
    DataFlowNode* node = graph_.FindNode(current);
    if (node) {
      for (DataFlowNode* driver : node->drivers) {
        if (visited.find(driver->name) == visited.end()) {
          queue.push(driver->name);
        }
      }
    }
  }
  
  return result;
}

absl::Status DataFlowAnalyzer::PropagateConstants() {
  // Mark parameters as constants (already done in ExtractParameters)
  
  // Propagate constant information through the graph
  for (auto& pair : graph_.nodes) {
    auto& node = pair.second;
    if (node.is_constant) {
      PropagateConstantsRecursive(node);
    }
  }
  
  return absl::OkStatus();
}

void DataFlowAnalyzer::PropagateConstantsRecursive(DataFlowNode& node) {
  // If all drivers of a node are constants, the node is also constant
  for (DataFlowNode* reader : node.readers) {
    if (!reader->is_constant) {
      bool all_drivers_constant = true;
      for (DataFlowNode* driver : reader->drivers) {
        if (!driver->is_constant) {
          all_drivers_constant = false;
          break;
        }
      }
      
      if (all_drivers_constant && !reader->drivers.empty()) {
        reader->is_constant = true;
        graph_.constant_list.push_back(reader->name);
        PropagateConstantsRecursive(*reader);
      }
    }
  }
}

bool DataFlowAnalyzer::IsConstantExpression(const verible::Symbol& expr) {
  // TODO: Implement constant expression analysis
  // For now, return false
  return false;
}

absl::Status DataFlowAnalyzer::AnalyzePortDataFlow() {
  // Analyze data flow through ports
  // TODO: Implement port data flow analysis
  return absl::OkStatus();
}

void DataFlowAnalyzer::AddError(const std::string& message,
                                const verible::Symbol* origin) {
  // TODO: Add file and line number information
  errors_.push_back(message);
}

void DataFlowAnalyzer::AddWarning(const std::string& message,
                                  const verible::Symbol* origin) {
  // TODO: Add file and line number information
  warnings_.push_back(message);
}

}  // namespace verilog

