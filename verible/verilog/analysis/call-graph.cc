// Copyright 2025 The Verible Authors.
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

#include "verible/verilog/analysis/call-graph.h"

#include <algorithm>
#include <sstream>
#include <stack>

#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"

namespace verilog {
namespace analysis {

CallGraph::CallGraph(const SymbolTable* symbol_table)
    : symbol_table_(symbol_table) {}

void CallGraph::Build() {
  // Build call graph by traversing symbol table
  Clear();
  
  if (!symbol_table_) return;
  
  // Traverse the symbol table root
  BuildFromNode(symbol_table_->Root());
}

void CallGraph::BuildFromNode(const SymbolTableNode& node) {
  const auto& info = node.Value();
  
  // If this is a function or task, add it as a node
  if (info.metatype == SymbolMetaType::kFunction ||
      info.metatype == SymbolMetaType::kTask) {
    // Use the declared name as the node name
    const auto* key = node.Key();
    if (key && !key->empty()) {
      std::string func_name(*key);
      AddNode(func_name);
      
      // Extract calls from this function/task's definition
      // Look through local_references_to_bind for call sites
      for (const auto& ref : info.local_references_to_bind) {
        if (!ref.Empty() && ref.components) {
          // Get the first component (simplified - doesn't traverse tree)
          const auto& first_component = ref.components->Value();
          if (!first_component.identifier.empty()) {
            // This is a potential call to another function
            std::string callee_name(first_component.identifier);
            
            // Add the edge if it looks like a call
            if (!callee_name.empty() && callee_name != func_name) {
              AddEdge(func_name, callee_name);
            }
          }
        }
      }
    }
  }
  
  // Recursively traverse children
  for (const auto& child : node) {
    BuildFromNode(child.second);
  }
}

void CallGraph::Clear() {
  nodes_.clear();
  adj_list_.clear();
  reverse_adj_list_.clear();
}

void CallGraph::AddNode(const std::string& name) {
  nodes_.insert(name);
}

void CallGraph::AddEdge(const std::string& caller, const std::string& callee) {
  AddNode(caller);
  AddNode(callee);
  adj_list_[caller].insert(callee);
  reverse_adj_list_[callee].insert(caller);
}

bool CallGraph::HasNode(const std::string& name) const {
  return nodes_.count(name) > 0;
}

bool CallGraph::HasEdge(const std::string& caller,
                        const std::string& callee) const {
  auto it = adj_list_.find(caller);
  if (it == adj_list_.end()) return false;
  return it->second.count(callee) > 0;
}

size_t CallGraph::GetEdgeCount() const {
  size_t count = 0;
  for (const auto& [caller, callees] : adj_list_) {
    count += callees.size();
  }
  return count;
}

std::vector<std::string> CallGraph::GetCallers(const std::string& name) const {
  auto it = reverse_adj_list_.find(name);
  if (it == reverse_adj_list_.end()) return {};
  return std::vector<std::string>(it->second.begin(), it->second.end());
}

std::vector<std::string> CallGraph::GetCallees(const std::string& name) const {
  auto it = adj_list_.find(name);
  if (it == adj_list_.end()) return {};
  return std::vector<std::string>(it->second.begin(), it->second.end());
}

// Week 6: Advanced Analysis

bool CallGraph::HasRecursion(const std::string& name) const {
  std::set<std::string> visited;
  std::set<std::string> rec_stack;
  return HasCycleDFS(name, visited, rec_stack);
}

bool CallGraph::HasCycleDFS(const std::string& node,
                            std::set<std::string>& visited,
                            std::set<std::string>& rec_stack) const {
  if (rec_stack.count(node)) return true;
  if (visited.count(node)) return false;
  
  visited.insert(node);
  rec_stack.insert(node);
  
  auto it = adj_list_.find(node);
  if (it != adj_list_.end()) {
    for (const auto& callee : it->second) {
      if (HasCycleDFS(callee, visited, rec_stack)) {
        return true;
      }
    }
  }
  
  rec_stack.erase(node);
  return false;
}

std::vector<std::vector<std::string>> CallGraph::GetCallHierarchy(
    const std::string& root) const {
  std::vector<std::vector<std::string>> hierarchy;
  std::vector<std::string> path;
  path.push_back(root);
  hierarchy.push_back(path);
  return hierarchy;
}

std::set<std::string> CallGraph::GetTransitiveCallees(
    const std::string& name) const {
  std::set<std::string> result;
  TransitiveDFS(name, result);
  result.erase(name); // Don't include the starting node
  return result;
}

void CallGraph::TransitiveDFS(const std::string& node,
                              std::set<std::string>& visited) const {
  if (visited.count(node)) return;
  visited.insert(node);
  
  auto it = adj_list_.find(node);
  if (it != adj_list_.end()) {
    for (const auto& callee : it->second) {
      TransitiveDFS(callee, visited);
    }
  }
}

std::vector<std::string> CallGraph::FindRootNodes() const {
  std::vector<std::string> roots;
  for (const auto& node : nodes_) {
    if (reverse_adj_list_.find(node) == reverse_adj_list_.end() ||
        reverse_adj_list_.at(node).empty()) {
      roots.push_back(node);
    }
  }
  return roots;
}

std::vector<std::string> CallGraph::FindLeafNodes() const {
  std::vector<std::string> leaves;
  for (const auto& node : nodes_) {
    if (adj_list_.find(node) == adj_list_.end() ||
        adj_list_.at(node).empty()) {
      leaves.push_back(node);
    }
  }
  return leaves;
}

size_t CallGraph::GetMaxCallDepth(const std::string& name) const {
  std::set<std::string> visited;
  return MaxDepthDFS(name, visited);
}

size_t CallGraph::MaxDepthDFS(const std::string& node,
                              std::set<std::string>& visited) const {
  if (visited.count(node)) return 0; // Cycle detection
  
  auto it = adj_list_.find(node);
  if (it == adj_list_.end() || it->second.empty()) {
    return 0; // Leaf node
  }
  
  visited.insert(node);
  size_t max_depth = 0;
  for (const auto& callee : it->second) {
    size_t depth = 1 + MaxDepthDFS(callee, visited);
    max_depth = std::max(max_depth, depth);
  }
  visited.erase(node);
  
  return max_depth;
}

std::vector<std::vector<std::string>> CallGraph::DetectCycles() const {
  std::vector<std::vector<std::string>> cycles;
  
  // Find all SCCs with size > 1 (those are cycles)
  auto sccs = FindStronglyConnectedComponents();
  for (const auto& scc : sccs) {
    if (scc.size() > 1) {
      std::vector<std::string> cycle(scc.begin(), scc.end());
      cycles.push_back(cycle);
    }
  }
  
  return cycles;
}

// Week 7: Visualization & Dead Code

std::string CallGraph::ExportToDOT() const {
  std::ostringstream oss;
  oss << "digraph CallGraph {\n";
  oss << "  rankdir=LR;\n";
  oss << "  node [shape=box];\n\n";
  
  // Add nodes
  for (const auto& node : nodes_) {
    oss << "  \"" << node << "\";\n";
  }
  oss << "\n";
  
  // Add edges
  for (const auto& [caller, callees] : adj_list_) {
    for (const auto& callee : callees) {
      oss << "  \"" << caller << "\" -> \"" << callee << "\";\n";
    }
  }
  
  oss << "}\n";
  return oss.str();
}

std::string CallGraph::ExportSubgraphToDOT(const std::string& root,
                                           size_t depth) const {
  std::ostringstream oss;
  oss << "digraph CallSubgraph {\n";
  oss << "  rankdir=LR;\n";
  oss << "  node [shape=box];\n\n";
  
  // Simplified: just include root and direct callees
  std::set<std::string> included_nodes;
  included_nodes.insert(root);
  
  auto it = adj_list_.find(root);
  if (it != adj_list_.end() && depth > 0) {
    for (const auto& callee : it->second) {
      included_nodes.insert(callee);
    }
  }
  
  // Add nodes
  for (const auto& node : included_nodes) {
    oss << "  \"" << node << "\";\n";
  }
  oss << "\n";
  
  // Add edges within subgraph
  for (const auto& [caller, callees] : adj_list_) {
    if (included_nodes.count(caller)) {
      for (const auto& callee : callees) {
        if (included_nodes.count(callee)) {
          oss << "  \"" << caller << "\" -> \"" << callee << "\";\n";
        }
      }
    }
  }
  
  oss << "}\n";
  return oss.str();
}

std::string CallGraph::ExportToJSON() const {
  std::ostringstream oss;
  oss << "{\n";
  oss << "  \"nodes\": [\n";
  
  // Add nodes
  bool first_node = true;
  for (const auto& node : nodes_) {
    if (!first_node) oss << ",\n";
    oss << "    {\"id\": \"" << node << "\"}";
    first_node = false;
  }
  oss << "\n  ],\n";
  
  // Add edges
  oss << "  \"edges\": [\n";
  bool first_edge = true;
  for (const auto& [caller, callees] : adj_list_) {
    for (const auto& callee : callees) {
      if (!first_edge) oss << ",\n";
      oss << "    {\"source\": \"" << caller << "\", \"target\": \"" 
          << callee << "\"}";
      first_edge = false;
    }
  }
  oss << "\n  ]\n";
  oss << "}\n";
  
  return oss.str();
}

std::vector<std::string> CallGraph::FindDeadCode() const {
  std::vector<std::string> dead_code;
  
  // Dead code = nodes that are never called (except roots which are entry points)
  // We consider a function dead if it's not a root AND has no callers
  auto roots = FindRootNodes();
  std::set<std::string> root_set(roots.begin(), roots.end());
  
  for (const auto& node : nodes_) {
    bool has_callers = (reverse_adj_list_.find(node) != reverse_adj_list_.end() &&
                        !reverse_adj_list_.at(node).empty());
    bool is_root = root_set.count(node) > 0;
    
    // If not a root and has no callers, it's dead (unless it's the ONLY node)
    if (!is_root && !has_callers && nodes_.size() > 1) {
      dead_code.push_back(node);
    }
  }
  
  return dead_code;
}

CallGraph::Metrics CallGraph::GetMetrics() const {
  Metrics m;
  m.node_count = nodes_.size();
  m.edge_count = GetEdgeCount();
  
  if (m.node_count > 0) {
    double total_out = 0;
    double total_in = 0;
    for (const auto& node : nodes_) {
      auto it = adj_list_.find(node);
      if (it != adj_list_.end()) {
        total_out += it->second.size();
      }
      auto rit = reverse_adj_list_.find(node);
      if (rit != reverse_adj_list_.end()) {
        total_in += rit->second.size();
      }
    }
    m.avg_out_degree = total_out / m.node_count;
    m.avg_in_degree = total_in / m.node_count;
  }
  
  // Max call depth: find max depth from all root nodes
  auto roots = FindRootNodes();
  for (const auto& root : roots) {
    size_t depth = GetMaxCallDepth(root);
    m.max_call_depth = std::max(m.max_call_depth, depth);
  }
  
  m.cycle_count = DetectCycles().size();
  
  return m;
}

std::vector<std::string> CallGraph::TopologicalSort() const {
  std::vector<std::string> sorted;
  std::set<std::string> visited;
  std::stack<std::string> stack;
  
  // DFS to create topological order
  std::function<void(const std::string&)> dfs = [&](const std::string& node) {
    if (visited.count(node)) return;
    visited.insert(node);
    
    auto it = adj_list_.find(node);
    if (it != adj_list_.end()) {
      for (const auto& callee : it->second) {
        dfs(callee);
      }
    }
    
    stack.push(node);
  };
  
  // Visit all nodes
  for (const auto& node : nodes_) {
    if (!visited.count(node)) {
      dfs(node);
    }
  }
  
  // Pop from stack to get topological order
  while (!stack.empty()) {
    sorted.push_back(stack.top());
    stack.pop();
  }
  
  return sorted;
}

std::vector<std::set<std::string>> CallGraph::FindStronglyConnectedComponents() const {
  std::vector<std::set<std::string>> sccs;
  std::map<std::string, int> indices;
  std::map<std::string, int> lowlinks;
  std::vector<std::string> stack;
  std::set<std::string> on_stack;
  int index = 0;
  
  for (const auto& node : nodes_) {
    if (indices.find(node) == indices.end()) {
      TarjanSCC(node, index, indices, lowlinks, stack, on_stack, sccs);
    }
  }
  
  return sccs;
}

void CallGraph::TarjanSCC(const std::string& node, int& index,
                          std::map<std::string, int>& indices,
                          std::map<std::string, int>& lowlinks,
                          std::vector<std::string>& stack,
                          std::set<std::string>& on_stack,
                          std::vector<std::set<std::string>>& sccs) const {
  indices[node] = index;
  lowlinks[node] = index;
  index++;
  stack.push_back(node);
  on_stack.insert(node);
  
  auto it = adj_list_.find(node);
  if (it != adj_list_.end()) {
    for (const auto& callee : it->second) {
      if (indices.find(callee) == indices.end()) {
        TarjanSCC(callee, index, indices, lowlinks, stack, on_stack, sccs);
        lowlinks[node] = std::min(lowlinks[node], lowlinks[callee]);
      } else if (on_stack.count(callee)) {
        lowlinks[node] = std::min(lowlinks[node], indices[callee]);
      }
    }
  }
  
  if (lowlinks[node] == indices[node]) {
    std::set<std::string> scc;
    std::string w;
    do {
      w = stack.back();
      stack.pop_back();
      on_stack.erase(w);
      scc.insert(w);
    } while (w != node);
    sccs.push_back(scc);
  }
}

}  // namespace analysis
}  // namespace verilog

