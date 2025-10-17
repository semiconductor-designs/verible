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

#include "verible/verilog/analysis/call-graph-enhancer.h"

#include <algorithm>
#include <map>
#include <queue>
#include <set>
#include <string>
#include <vector>

#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/status/status.h"
#include "verible/common/analysis/syntax-tree-search.h"
#include "verible/common/text/concrete-syntax-leaf.h"
#include "verible/common/text/symbol.h"
#include "verible/common/util/casts.h"
#include "verible/verilog/CST/functions.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {

// CallGraphEnhancer implementation

CallGraphEnhancer::CallGraphEnhancer(const SymbolTable& symbol_table,
                                     const VerilogProject& project)
    : symbol_table_(symbol_table),
      project_(project),
      detect_dpi_(true),
      max_call_depth_(100) {
  // project_ will be used for cross-file analysis in future enhancements
  (void)project_;
}

CallGraphEnhancer::~CallGraphEnhancer() {
  // Automatic cleanup with unique_ptr - no manual deletes needed
}

absl::Status CallGraphEnhancer::BuildEnhancedCallGraph() {
  // Clear previous results (unique_ptr handles deletion automatically)
  nodes_.clear();
  edges_.clear();
  name_to_node_.clear();
  recursion_cycles_.clear();
  warnings_.clear();
  errors_.clear();
  
  // Build call graph step by step
  auto status = ExtractFunctions();
  if (!status.ok()) return status;
  
  status = ExtractTasks();
  if (!status.ok()) return status;
  
  status = ExtractCallSites();
  if (!status.ok()) return status;
  
  status = BuildCallEdges();
  if (!status.ok()) return status;
  
  status = DetectRecursion();
  if (!status.ok()) return status;
  
  status = IdentifyEntryPoints();
  if (!status.ok()) return status;
  
  status = ComputeCallDepths();
  if (!status.ok()) return status;
  
  status = FindUnreachableFunctions();
  if (!status.ok()) return status;
  
  // Compute statistics
  ComputeStatistics();
  
  return absl::OkStatus();
}

absl::Status CallGraphEnhancer::ExtractFunctions() {
  // Traverse symbol table root
  const auto& root = symbol_table_.Root();
  
  // Recursively traverse to find functions
  TraverseSymbolTable(root, "");
  
  return absl::OkStatus();
}

absl::Status CallGraphEnhancer::ExtractTasks() {
  // Tasks are extracted during TraverseSymbolTable along with functions
  // This method is separate for clarity and future enhancements
  return absl::OkStatus();
}

absl::Status CallGraphEnhancer::ExtractCallSites() {
  // For each function node, find call sites in its body
  for (const auto& node : nodes_) {
    FindCallsInFunction(node.get());
  }
  return absl::OkStatus();
}

absl::Status CallGraphEnhancer::BuildCallEdges() {
  // Build edges based on call sites
  for (const auto& caller : nodes_) {
    for (const auto* call_site : caller->call_sites) {
      // Extract called function name from call site
      std::string callee_name = ExtractCalledFunction(*call_site);
      
      if (callee_name.empty()) continue;
      
      // Find callee node
      auto* callee = FindNode(callee_name);
      if (!callee) {
        // Function not found - may be external or system function
        AddWarning(absl::StrCat("Called function '", callee_name, "' not found"));
        continue;
      }
      
      // Create edge
      auto edge = CreateEdge(caller.get(), callee, call_site);
      AddEdge(std::move(edge));
      
      // Update caller/callee relationships
      caller->callees.push_back(callee);
      callee->callers.push_back(caller.get());
    }
  }
  return absl::OkStatus();
}

absl::Status CallGraphEnhancer::DetectRecursion() {
  std::set<CallGraphNode*> visited;
  std::vector<CallGraphNode*> rec_stack;
  
  // Run DFS from each unvisited node
  for (const auto& node : nodes_) {
    if (visited.find(node.get()) == visited.end()) {
      DetectRecursionDFS(node.get(), visited, rec_stack);
    }
  }
  
  return absl::OkStatus();
}

absl::Status CallGraphEnhancer::ComputeCallDepths() {
  // Initialize all depths to 0
  for (const auto& node : nodes_) {
    node->call_depth = 0;
  }
  
  // Compute depth as "maximum path length from this node to leaf nodes"
  // Leaf nodes (no callees) have depth 0
  // Entry points have the highest depths
  
  // Use BFS from leaf nodes upward through callers
  std::queue<CallGraphNode*> queue;
  std::set<CallGraphNode*> in_queue;
  
  // Start with all leaf nodes (no callees)
  for (const auto& node : nodes_) {
    if (node->callees.empty()) {
      node->call_depth = 0;
      queue.push(node.get());
      in_queue.insert(node.get());
    }
  }
  
  // BFS upward through callers
  while (!queue.empty()) {
    auto* node = queue.front();
    queue.pop();
    in_queue.erase(node);
    
    // Update all callers' depths
    for (auto* caller : node->callers) {
      int new_depth = node->call_depth + 1;
      
      // Update if we found a longer path
      if (new_depth > caller->call_depth) {
        caller->call_depth = new_depth;
        
        // Re-queue if not already queued
        if (in_queue.find(caller) == in_queue.end()) {
          queue.push(caller);
          in_queue.insert(caller);
        }
      }
    }
  }
  
  return absl::OkStatus();
}

absl::Status CallGraphEnhancer::IdentifyEntryPoints() {
  for (const auto& node : nodes_) {
    if (IsEntryPoint(node.get())) {
      node->is_entry_point = true;
      statistics_.entry_points++;
    }
  }
  return absl::OkStatus();
}

absl::Status CallGraphEnhancer::FindUnreachableFunctions() {
  for (const auto& node : nodes_) {
    // Unreachable if: no callers AND not an entry point AND not DPI
    if (node->callers.empty() && !node->is_entry_point && !node->is_dpi) {
      node->is_unreachable = true;
      statistics_.unreachable_functions++;
    }
  }
  return absl::OkStatus();
}

// Query methods

std::vector<CallGraphNode*> CallGraphEnhancer::GetAllNodes() const {
  std::vector<CallGraphNode*> result;
  result.reserve(nodes_.size());
  for (const auto& node : nodes_) {
    result.push_back(node.get());
  }
  return result;
}

std::vector<CallGraphEdge*> CallGraphEnhancer::GetAllEdges() const {
  std::vector<CallGraphEdge*> result;
  result.reserve(edges_.size());
  for (const auto& edge : edges_) {
    result.push_back(edge.get());
  }
  return result;
}

std::vector<CallGraphNode*> CallGraphEnhancer::GetEntryPoints() const {
  std::vector<CallGraphNode*> entry_points;
  for (const auto& node : nodes_) {
    if (node->is_entry_point) {
      entry_points.push_back(node.get());
    }
  }
  return entry_points;
}

std::vector<CallGraphNode*> CallGraphEnhancer::GetUnreachableFunctions() const {
  std::vector<CallGraphNode*> unreachable;
  for (const auto& node : nodes_) {
    if (node->is_unreachable) {
      unreachable.push_back(node.get());
    }
  }
  return unreachable;
}

CallGraphNode* CallGraphEnhancer::GetNode(const std::string& function_name) const {
  return FindNode(function_name);
}

std::vector<CallGraphNode*> CallGraphEnhancer::GetCallers(const std::string& function_name) const {
  auto* node = FindNode(function_name);
  if (!node) return {};
  return node->callers;
}

std::vector<CallGraphNode*> CallGraphEnhancer::GetCallees(const std::string& function_name) const {
  auto* node = FindNode(function_name);
  if (!node) return {};
  return node->callees;
}

int CallGraphEnhancer::GetCallDepth(const std::string& function_name) const {
  auto* node = FindNode(function_name);
  if (!node) return -1;
  return node->call_depth;
}

bool CallGraphEnhancer::IsRecursive(const std::string& function_name) const {
  auto* node = FindNode(function_name);
  if (!node) return false;
  return node->is_recursive;
}

// Private methods

std::unique_ptr<CallGraphNode> CallGraphEnhancer::CreateNode(const std::string& name, 
                                                             CallGraphNode::NodeType type) {
  auto node = std::make_unique<CallGraphNode>();
  node->name = name;
  node->fully_qualified_name = name;
  node->type = type;
  return node;
}

CallGraphNode* CallGraphEnhancer::FindNode(const std::string& name) const {
  auto it = name_to_node_.find(name);
  if (it != name_to_node_.end()) {
    return it->second;
  }
  return nullptr;
}

void CallGraphEnhancer::AddNode(std::unique_ptr<CallGraphNode> node) {
  CallGraphNode* raw_ptr = node.get();
  nodes_.push_back(std::move(node));
  name_to_node_[raw_ptr->name] = raw_ptr;
  
  // Update statistics
  if (raw_ptr->type == CallGraphNode::kFunction) {
    statistics_.total_functions++;
  } else if (raw_ptr->type == CallGraphNode::kTask) {
    statistics_.total_tasks++;
  }
  statistics_.total_nodes++;
}

std::unique_ptr<CallGraphEdge> CallGraphEnhancer::CreateEdge(CallGraphNode* caller, 
                                                             CallGraphNode* callee,
                                                             const verible::Symbol* call_site) {
  auto edge = std::make_unique<CallGraphEdge>();
  edge->caller = caller;
  edge->callee = callee;
  edge->call_site = call_site;
  edge->call_type = CallGraphEdge::kDirect;
  return edge;
}

void CallGraphEnhancer::AddEdge(std::unique_ptr<CallGraphEdge> edge) {
  edges_.push_back(std::move(edge));
  statistics_.total_edges++;
  statistics_.direct_calls++;
}

void CallGraphEnhancer::TraverseSymbolTable(const SymbolTableNode& node, 
                                            const std::string& scope) {
  // Check if this node is a function or task
  const auto& info = node.Value();
  
  if (info.metatype == SymbolMetaType::kFunction) {
    ExtractFunctionNode(node, scope);
  } else if (info.metatype == SymbolMetaType::kTask) {
    ExtractTaskNode(node, scope);
  }
  
  // Recursively traverse children
  std::string new_scope = scope;
  if (node.Key()) {
    if (!scope.empty()) {
      new_scope = absl::StrCat(scope, ".", std::string(*node.Key()));
    } else {
      new_scope = std::string(*node.Key());
    }
  }
  
  for (const auto& child : node.Children()) {
    TraverseSymbolTable(child.second, new_scope);
  }
}

void CallGraphEnhancer::ExtractFunctionNode(const SymbolTableNode& node, 
                                            const std::string& scope) {
  if (!node.Key()) return;
  
  std::string name = std::string(*node.Key());
  const auto& info = node.Value();
  
  // Create function node
  auto func_node = CreateNode(name, CallGraphNode::kFunction);
  func_node->syntax_origin = info.syntax_origin;
  func_node->file = info.file_origin;
  
  // Add to graph
  AddNode(std::move(func_node));
}

void CallGraphEnhancer::ExtractTaskNode(const SymbolTableNode& node, 
                                        const std::string& scope) {
  if (!node.Key()) return;
  
  std::string name = std::string(*node.Key());
  const auto& info = node.Value();
  
  // Create task node
  auto task_node = CreateNode(name, CallGraphNode::kTask);
  task_node->syntax_origin = info.syntax_origin;
  task_node->file = info.file_origin;
  
  // Add to graph
  AddNode(std::move(task_node));
}

void CallGraphEnhancer::FindCallsInFunction(CallGraphNode* function) {
  if (!function || !function->syntax_origin) return;
  
  // Get function body from CST
  const auto* func_body = GetFunctionBlockStatementList(*function->syntax_origin);
  if (!func_body) return;
  
  // Find all function/task calls in the body using Verible API
  auto call_matches = FindAllFunctionOrTaskCalls(*func_body);
  
  // Store call sites
  for (const auto& call : call_matches) {
    function->call_sites.push_back(call.match);
  }
}

bool CallGraphEnhancer::IsCallExpression(const verible::Symbol& symbol) {
  // Check if this is a Node (not a Leaf)
  if (symbol.Kind() != verible::SymbolKind::kNode) {
    return false;
  }
  
  // Cast to Node and check tag
  const auto& node = verible::SymbolCastToNode(symbol);
  return static_cast<NodeEnum>(node.Tag().tag) == NodeEnum::kFunctionCall;
}

std::string CallGraphEnhancer::ExtractCalledFunction(const verible::Symbol& call_expr) {
  // Try the primary API first
  const auto* name_leaf = GetFunctionCallName(call_expr);
  if (name_leaf) {
    return std::string(name_leaf->get().text());
  }
  
  // Fallback: Try to get identifiers directly from the function call
  const auto* identifiers = GetIdentifiersFromFunctionCall(call_expr);
  if (identifiers && identifiers->Kind() == verible::SymbolKind::kNode) {
    // Try to find an identifier leaf in the identifiers subtree
    const auto& id_node = verible::SymbolCastToNode(*identifiers);
    for (const auto& child : id_node.children()) {
      if (child && child->Kind() == verible::SymbolKind::kLeaf) {
        const auto& leaf = verible::SymbolCastToLeaf(*child);
        std::string text(leaf.get().text());
        if (!text.empty()) {
          return text;
        }
      }
    }
  }
  
  return "";
}

void CallGraphEnhancer::DetectRecursionDFS(CallGraphNode* node, 
                                           std::set<CallGraphNode*>& visited,
                                           std::vector<CallGraphNode*>& rec_stack) {
  visited.insert(node);
  rec_stack.push_back(node);
  
  // Visit all callees
  for (auto* callee : node->callees) {
    if (visited.find(callee) == visited.end()) {
      // Not visited yet - recurse
      DetectRecursionDFS(callee, visited, rec_stack);
    } else if (IsInRecursionStack(callee, rec_stack)) {
      // Found a cycle!
      RecursionCycle cycle;
      
      // Extract cycle from rec_stack
      auto it = std::find(rec_stack.begin(), rec_stack.end(), callee);
      if (it != rec_stack.end()) {
        cycle.cycle_nodes.assign(it, rec_stack.end());
        cycle.cycle_length = cycle.cycle_nodes.size();
        cycle.entry_node = callee;
        
        // Determine cycle type
        if (cycle.cycle_length == 1) {
          cycle.cycle_type = RecursionCycle::kDirect;
          statistics_.direct_recursion++;
        } else {
          cycle.cycle_type = RecursionCycle::kIndirect;
          statistics_.indirect_recursion++;
        }
        
        recursion_cycles_.push_back(cycle);
        statistics_.recursion_cycles++;
        
        // Mark all nodes in cycle as recursive
        MarkRecursiveCycle(cycle.cycle_nodes);
      }
    }
  }
  
  // Remove from recursion stack
  rec_stack.pop_back();
}

bool CallGraphEnhancer::IsInRecursionStack(CallGraphNode* node, 
                                           const std::vector<CallGraphNode*>& rec_stack) {
  return std::find(rec_stack.begin(), rec_stack.end(), node) != rec_stack.end();
}

void CallGraphEnhancer::MarkRecursiveCycle(const std::vector<CallGraphNode*>& cycle) {
  for (auto* node : cycle) {
    if (!node->is_recursive) {
      node->is_recursive = true;
      statistics_.recursive_functions++;
    }
  }
}


bool CallGraphEnhancer::IsEntryPoint(CallGraphNode* node) {
  // Entry point if: no callers AND has callees (participates in call graph)
  // Orphan functions (no callers, no callees) are unreachable, not entry points
  return node->callers.empty() && !node->callees.empty();
}

void CallGraphEnhancer::ComputeStatistics() {
  // Find max call depth
  for (const auto& node : nodes_) {
    if (node->call_depth > statistics_.max_call_depth) {
      statistics_.max_call_depth = node->call_depth;
    }
  }
  
  // Compute average call depth
  int total_depth = 0;
  for (const auto& node : nodes_) {
    total_depth += node->call_depth;
  }
  if (statistics_.total_nodes > 0) {
    statistics_.avg_call_depth = 
        static_cast<float>(total_depth) / statistics_.total_nodes;
  }
}

void CallGraphEnhancer::AddWarning(const std::string& message) {
  warnings_.push_back(message);
}

void CallGraphEnhancer::AddError(const std::string& message) {
  errors_.push_back(message);
}

}  // namespace verilog

