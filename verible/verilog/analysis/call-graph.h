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

#ifndef VERIBLE_VERILOG_ANALYSIS_CALL_GRAPH_H_
#define VERIBLE_VERILOG_ANALYSIS_CALL_GRAPH_H_

#include <map>
#include <set>
#include <string>
#include <vector>

#include "verible/verilog/analysis/symbol-table.h"

namespace verilog {
namespace analysis {

// CallGraph represents the call relationships between functions and tasks
// in SystemVerilog code. It supports:
// - Call extraction from symbol table
// - Recursion detection
// - Dead code analysis
// - Visualization (DOT export)
// - Complexity metrics
//
// Usage:
//   CallGraph graph(&symbol_table);
//   graph.Build();  // Extract calls from code
//   
//   if (graph.HasRecursion("my_func")) {
//     std::cout << "my_func is recursive!\n";
//   }
//   
//   auto dead_code = graph.FindDeadCode();
//   std::string dot = graph.ExportToDOT();
class CallGraph {
 public:
  // Graph metrics for complexity analysis
  struct Metrics {
    size_t node_count = 0;
    size_t edge_count = 0;
    double avg_out_degree = 0.0;
    double avg_in_degree = 0.0;
    size_t max_call_depth = 0;
    size_t cycle_count = 0;
  };
  
  // Construct CallGraph with a symbol table
  explicit CallGraph(const SymbolTable* symbol_table);
  
  // Build the call graph by analyzing the symbol table
  void Build();
  
  // Clear all nodes and edges
  void Clear();
  
  // Week 5: Foundation APIs
  
  // Add a node (function/task) to the graph
  void AddNode(const std::string& name);
  
  // Add a directed edge from caller to callee
  void AddEdge(const std::string& caller, const std::string& callee);
  
  // Check if node exists
  bool HasNode(const std::string& name) const;
  
  // Check if edge exists
  bool HasEdge(const std::string& caller, const std::string& callee) const;
  
  // Get number of nodes
  size_t GetNodeCount() const { return nodes_.size(); }
  
  // Get number of edges
  size_t GetEdgeCount() const;
  
  // Get all callers of a function
  std::vector<std::string> GetCallers(const std::string& name) const;
  
  // Get all callees of a function
  std::vector<std::string> GetCallees(const std::string& name) const;
  
  // Week 6: Advanced Analysis APIs
  
  // Check if a function is recursive (direct or indirect)
  bool HasRecursion(const std::string& name) const;
  
  // Get call hierarchy starting from a function
  std::vector<std::vector<std::string>> GetCallHierarchy(
      const std::string& root) const;
  
  // Get all transitive callees (everything reachable from this function)
  std::set<std::string> GetTransitiveCallees(const std::string& name) const;
  
  // Find root nodes (functions never called by others)
  std::vector<std::string> FindRootNodes() const;
  
  // Find leaf nodes (functions that call nothing)
  std::vector<std::string> FindLeafNodes() const;
  
  // Get maximum call depth from a function
  size_t GetMaxCallDepth(const std::string& name) const;
  
  // Detect all cycles in the graph
  std::vector<std::vector<std::string>> DetectCycles() const;
  
  // Week 7: Visualization & Dead Code APIs
  
  // Export graph to DOT format for Graphviz
  std::string ExportToDOT() const;
  
  // Export subgraph rooted at a function with depth limit
  std::string ExportSubgraphToDOT(const std::string& root, size_t depth) const;
  
  // Export graph to JSON format
  std::string ExportToJSON() const;
  
  // Find dead code (functions never called)
  std::vector<std::string> FindDeadCode() const;
  
  // Compute complexity metrics
  Metrics GetMetrics() const;
  
  // Topological sort (if graph is acyclic)
  std::vector<std::string> TopologicalSort() const;
  
  // Find strongly connected components
  std::vector<std::set<std::string>> FindStronglyConnectedComponents() const;
  
 private:
  const SymbolTable* symbol_table_;
  
  // Nodes: function/task names
  std::set<std::string> nodes_;
  
  // Adjacency list: caller -> set of callees
  std::map<std::string, std::set<std::string>> adj_list_;
  
  // Reverse adjacency list: callee -> set of callers
  std::map<std::string, std::set<std::string>> reverse_adj_list_;
  
  // Helper: DFS for recursion detection
  bool HasCycleDFS(const std::string& node,
                   std::set<std::string>& visited,
                   std::set<std::string>& rec_stack) const;
  
  // Helper: DFS for transitive closure
  void TransitiveDFS(const std::string& node,
                     std::set<std::string>& visited) const;
  
  // Helper: Compute max depth via DFS
  size_t MaxDepthDFS(const std::string& node,
                     std::set<std::string>& visited) const;
  
  // Helper: Tarjan's algorithm for SCCs
  void TarjanSCC(const std::string& node, int& index,
                 std::map<std::string, int>& indices,
                 std::map<std::string, int>& lowlinks,
                 std::vector<std::string>& stack,
                 std::set<std::string>& on_stack,
                 std::vector<std::set<std::string>>& sccs) const;
};

}  // namespace analysis
}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_CALL_GRAPH_H_

