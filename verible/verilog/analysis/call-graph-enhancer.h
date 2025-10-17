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

#ifndef VERIBLE_VERILOG_ANALYSIS_CALL_GRAPH_ENHANCER_H_
#define VERIBLE_VERILOG_ANALYSIS_CALL_GRAPH_ENHANCER_H_

#include <map>
#include <set>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "verible/common/text/symbol.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {

// Forward declarations
struct CallGraphNode;
struct CallGraphEdge;

// Represents a function or task in the call graph
struct CallGraphNode {
  // Identity
  std::string name;                          // Function/task name
  std::string fully_qualified_name;          // Full hierarchical name
  
  // Source information
  const verible::Symbol* syntax_origin;      // CST node where defined
  const VerilogSourceFile* file;             // Source file
  int line_number;                           // Line number
  
  // Type
  enum NodeType {
    kFunction,          // Function
    kTask,              // Task
    kDPIFunction,       // DPI function
    kSystemFunction,    // System function
    kVirtualFunction    // Virtual function
  } type;
  
  // Call relationships
  std::vector<CallGraphNode*> callers;       // Who calls this function
  std::vector<CallGraphNode*> callees;       // Who this function calls
  
  // Call sites
  std::vector<const verible::Symbol*> call_sites;  // Where calls occur
  
  // Analysis results
  bool is_entry_point;                       // Top-level (no callers)
  bool is_unreachable;                       // Never called
  bool is_recursive;                         // Part of recursion cycle
  bool is_dpi;                               // DPI function
  bool is_virtual;                           // Virtual function
  int call_depth;                            // Max depth from entry points
  int recursive_depth;                       // Recursion depth
  
  // Constructor
  CallGraphNode()
      : syntax_origin(nullptr),
        file(nullptr),
        line_number(0),
        type(kFunction),
        is_entry_point(false),
        is_unreachable(false),
        is_recursive(false),
        is_dpi(false),
        is_virtual(false),
        call_depth(0),
        recursive_depth(0) {}
};

// Represents a call relationship between functions/tasks
struct CallGraphEdge {
  CallGraphNode* caller;                     // Calling function
  CallGraphNode* callee;                     // Called function
  const verible::Symbol* call_site;          // Where the call occurs
  
  // Call type
  enum CallType {
    kDirect,            // Direct call
    kIndirect,          // Indirect call
    kRecursive          // Recursive call
  } call_type;
  
  // Constructor
  CallGraphEdge()
      : caller(nullptr),
        callee(nullptr),
        call_site(nullptr),
        call_type(kDirect) {}
};

// Represents a detected recursion cycle
struct RecursionCycle {
  std::vector<CallGraphNode*> cycle_nodes;   // Nodes in the cycle
  std::vector<CallGraphEdge*> cycle_edges;   // Edges in the cycle
  
  enum CycleType {
    kDirect,            // f() calls f()
    kIndirect           // f() -> g() -> f()
  } cycle_type;
  
  int cycle_length;                          // Number of nodes
  CallGraphNode* entry_node;                 // Where cycle starts
  
  // Constructor
  RecursionCycle()
      : cycle_type(kDirect),
        cycle_length(0),
        entry_node(nullptr) {}
};

// Tracks detailed call graph statistics
struct CallGraphStatistics {
  // Counts
  int total_functions;
  int total_tasks;
  int total_nodes;
  int total_edges;
  
  int entry_points;
  int unreachable_functions;
  int recursive_functions;
  int dpi_functions;
  int virtual_functions;
  
  int direct_calls;
  int indirect_calls;
  
  int recursion_cycles;
  int direct_recursion;
  int indirect_recursion;
  
  int max_call_depth;
  float avg_call_depth;
  
  // Constructor
  CallGraphStatistics()
      : total_functions(0),
        total_tasks(0),
        total_nodes(0),
        total_edges(0),
        entry_points(0),
        unreachable_functions(0),
        recursive_functions(0),
        dpi_functions(0),
        virtual_functions(0),
        direct_calls(0),
        indirect_calls(0),
        recursion_cycles(0),
        direct_recursion(0),
        indirect_recursion(0),
        max_call_depth(0),
        avg_call_depth(0.0f) {}
};

// Enhanced call graph analyzer for SystemVerilog
class CallGraphEnhancer {
 public:
  // Constructor
  CallGraphEnhancer(const SymbolTable& symbol_table,
                    const VerilogProject& project);
  
  // Destructor
  ~CallGraphEnhancer();
  
  // Main analysis entry point
  absl::Status BuildEnhancedCallGraph();
  
  // Specific analysis methods
  absl::Status ExtractFunctions();
  absl::Status ExtractTasks();
  absl::Status ExtractCallSites();
  absl::Status BuildCallEdges();
  absl::Status DetectRecursion();
  absl::Status ComputeCallDepths();
  absl::Status IdentifyEntryPoints();
  absl::Status FindUnreachableFunctions();
  
  // Query methods
  std::vector<CallGraphNode*> GetAllNodes() const;
  std::vector<CallGraphEdge*> GetAllEdges() const;
  std::vector<CallGraphNode*> GetEntryPoints() const;
  std::vector<CallGraphNode*> GetUnreachableFunctions() const;
  std::vector<RecursionCycle> GetRecursionCycles() const { return recursion_cycles_; }
  CallGraphStatistics GetStatistics() const { return statistics_; }
  
  // Specific queries
  CallGraphNode* GetNode(const std::string& function_name) const;
  std::vector<CallGraphNode*> GetCallers(const std::string& function_name) const;
  std::vector<CallGraphNode*> GetCallees(const std::string& function_name) const;
  int GetCallDepth(const std::string& function_name) const;
  bool IsRecursive(const std::string& function_name) const;
  
  // Configuration
  void SetDetectDPIFunctions(bool detect) { detect_dpi_ = detect; }
  void SetMaxCallDepth(int max_depth) { max_call_depth_ = max_depth; }
  
  // Error/warning reporting
  std::vector<std::string> GetWarnings() const { return warnings_; }
  std::vector<std::string> GetErrors() const { return errors_; }
  
 private:
  // Node management
  std::unique_ptr<CallGraphNode> CreateNode(const std::string& name, CallGraphNode::NodeType type);
  CallGraphNode* FindNode(const std::string& name) const;
  void AddNode(std::unique_ptr<CallGraphNode> node);
  
  // Edge management
  std::unique_ptr<CallGraphEdge> CreateEdge(CallGraphNode* caller, CallGraphNode* callee,
                                            const verible::Symbol* call_site);
  void AddEdge(std::unique_ptr<CallGraphEdge> edge);
  
  // Traversal helpers
  void TraverseSymbolTable(const SymbolTableNode& node, const std::string& scope);
  void ExtractFunctionNode(const SymbolTableNode& node, const std::string& scope);
  void ExtractTaskNode(const SymbolTableNode& node, const std::string& scope);
  
  // Call site detection
  void FindCallsInFunction(CallGraphNode* function);
  bool IsCallExpression(const verible::Symbol& symbol);
  std::string ExtractCalledFunction(const verible::Symbol& call_expr);
  
  // Recursion detection
  void DetectRecursionDFS(CallGraphNode* node, 
                          std::set<CallGraphNode*>& visited,
                          std::vector<CallGraphNode*>& rec_stack);
  bool IsInRecursionStack(CallGraphNode* node, 
                          const std::vector<CallGraphNode*>& rec_stack);
  void MarkRecursiveCycle(const std::vector<CallGraphNode*>& cycle);
  
  // Depth computation
  void ComputeDepthBFS(CallGraphNode* entry_point);
  
  // Entry point detection
  bool IsEntryPoint(CallGraphNode* node);
  
  // Statistics
  void ComputeStatistics();
  
  // Warning/error reporting
  void AddWarning(const std::string& message);
  void AddError(const std::string& message);
  
  // Member variables
  const SymbolTable& symbol_table_;
  const VerilogProject& project_;
  std::vector<std::unique_ptr<CallGraphNode>> nodes_;
  std::vector<std::unique_ptr<CallGraphEdge>> edges_;
  std::map<std::string, CallGraphNode*> name_to_node_;  // Raw pointers for lookup
  std::vector<RecursionCycle> recursion_cycles_;
  CallGraphStatistics statistics_;
  std::vector<std::string> warnings_;
  std::vector<std::string> errors_;
  
  // Configuration
  bool detect_dpi_;
  int max_call_depth_;
};

}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_CALL_GRAPH_ENHANCER_H_

