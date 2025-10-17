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

#ifndef VERIBLE_VERILOG_ANALYSIS_DATA_FLOW_ANALYZER_H_
#define VERIBLE_VERILOG_ANALYSIS_DATA_FLOW_ANALYZER_H_

#include <string>
#include <unordered_map>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "verible/common/text/symbol.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {

// Forward declarations
struct DataFlowNode;
struct DataFlowEdge;
class DataFlowGraph;

// Represents a signal, variable, port, or parameter in the design
struct DataFlowNode {
  // Identity
  std::string name;              // Full hierarchical name
  std::string local_name;        // Local name within scope
  
  // Source information
  const verible::Symbol* syntax_origin;  // CST node where declared
  const VerilogSourceFile* file;         // Source file
  int line_number;                       // Line number
  
  // Type information
  enum NodeType {
    kSignal,            // wire, reg, logic
    kVariable,          // local variable (function/task)
    kPort,              // input, output, inout
    kParameter,         // parameter, localparam
    kConstant           // literal constant
  } type;
  
  // Data flow relationships
  std::vector<DataFlowNode*> drivers;        // Nodes that drive this
  std::vector<DataFlowNode*> readers;        // Nodes that read from this
  std::vector<DataFlowEdge*> incoming_edges; // Incoming edges
  std::vector<DataFlowEdge*> outgoing_edges; // Outgoing edges
  
  // Properties
  bool is_constant;        // Compile-time constant
  bool is_parameter;       // Is a parameter
  bool has_multi_driver;   // Multiple drivers (conflict)
  bool is_port;            // Is a port
  bool is_read;            // Ever read from
  bool is_written;         // Ever written to
  int fanout;              // Number of readers
  int driver_count;        // Number of drivers
  
  // Scope information
  std::string scope;                         // Hierarchical scope
  const SymbolTableNode* symbol_node;        // Symbol table node
  
  // Constructor
  DataFlowNode()
      : syntax_origin(nullptr),
        file(nullptr),
        line_number(0),
        type(kSignal),
        is_constant(false),
        is_parameter(false),
        has_multi_driver(false),
        is_port(false),
        is_read(false),
        is_written(false),
        fanout(0),
        driver_count(0),
        symbol_node(nullptr) {}
};

// Represents a data flow connection between two nodes
struct DataFlowEdge {
  // Endpoints
  DataFlowNode* source;      // Source node (driver)
  DataFlowNode* target;      // Target node (driven)
  
  // Assignment information
  const verible::Symbol* assignment_origin;  // Assignment CST node
  const VerilogSourceFile* file;             // Source file
  int line_number;                           // Line number
  
  // Edge type
  enum EdgeType {
    kBlocking,          // Blocking assignment (=)
    kNonBlocking,       // Non-blocking assignment (<=)
    kContinuous,        // Continuous assignment (assign)
    kPortConnection,    // Module port connection
    kFunctionReturn,    // Function return value
    kFunctionArg        // Function argument
  } type;
  
  // Conditional information
  bool is_conditional;       // Inside if/case
  std::string condition;     // Condition expression (if any)
  
  // Properties
  bool is_complete_driver;   // Drives all bits
  bool is_partial_driver;    // Drives some bits
  
  // Constructor
  DataFlowEdge()
      : source(nullptr),
        target(nullptr),
        assignment_origin(nullptr),
        file(nullptr),
        line_number(0),
        type(kBlocking),
        is_conditional(false),
        is_complete_driver(true),
        is_partial_driver(false) {}
};

// The complete data flow graph for a design
class DataFlowGraph {
 public:
  DataFlowGraph() = default;
  
  // Nodes
  std::unordered_map<std::string, DataFlowNode> nodes;
  
  // Edges
  std::vector<DataFlowEdge> edges;
  
  // Organized by type
  std::vector<DataFlowNode*> signals;
  std::vector<DataFlowNode*> variables;
  std::vector<DataFlowNode*> ports;
  std::vector<DataFlowNode*> parameters;
  std::vector<DataFlowNode*> constants;
  
  // Analysis results
  std::vector<DataFlowNode*> multi_driver_nodes;    // Nodes with multiple drivers
  std::vector<DataFlowNode*> undriven_nodes;        // Nodes never written
  std::vector<DataFlowNode*> unread_nodes;          // Nodes never read
  std::vector<std::string> constant_list;           // Compile-time constants
  
  // Dependency chains
  std::unordered_map<std::string, std::vector<std::string>> dependencies;
  
  // Methods
  DataFlowNode* FindNode(const std::string& name);
  void AddEdge(DataFlowNode* source, DataFlowNode* target, 
               DataFlowEdge::EdgeType type);
  std::vector<DataFlowNode*> GetDriversOf(const std::string& name);
  std::vector<DataFlowNode*> GetReadersOf(const std::string& name);
  std::vector<std::string> GetDependencyChain(const std::string& name);
  bool HasMultiDriver(const std::string& name);
  size_t NodeCount() const { return nodes.size(); }
  size_t EdgeCount() const { return edges.size(); }
};

// Analyzes data flow through SystemVerilog designs
class DataFlowAnalyzer {
 public:
  // Constructor
  DataFlowAnalyzer(const SymbolTable& symbol_table,
                   const VerilogProject& project);
  
  // Main analysis entry point
  absl::Status AnalyzeDataFlow();
  
  // Build the data flow graph
  absl::Status BuildDataFlowGraph();
  
  // Query methods
  const DataFlowGraph& GetDataFlowGraph() const { return graph_; }
  std::vector<DataFlowNode*> GetDriversOf(const std::string& signal_name);
  std::vector<DataFlowNode*> GetReadersOf(const std::string& signal_name);
  std::vector<std::string> GetDependencyChain(const std::string& signal_name);
  
  // Analysis methods
  absl::Status DetectMultiDrivers();
  absl::Status AnalyzeDependencies();
  absl::Status PropagateConstants();
  absl::Status AnalyzePortDataFlow();
  
  // Error/warning reporting
  std::vector<std::string> GetErrors() const { return errors_; }
  std::vector<std::string> GetWarnings() const { return warnings_; }
  
 private:
  // Symbol table traversal
  void TraverseSymbolTable(const SymbolTableNode& node, 
                           const std::string& scope);
  
  // Node extraction
  void ExtractSignals(const SymbolTableNode& node, const std::string& scope);
  void ExtractVariables(const SymbolTableNode& node, const std::string& scope);
  void ExtractPorts(const SymbolTableNode& node, const std::string& scope);
  void ExtractParameters(const SymbolTableNode& node, const std::string& scope);
  
  // Assignment extraction
  void ExtractAssignments(const SymbolTableNode& node);
  void ExtractBlockingAssignments(const verible::Symbol& syntax);
  void ExtractNonBlockingAssignments(const verible::Symbol& syntax);
  void ExtractContinuousAssignments(const verible::Symbol& syntax);
  void ExtractPortConnections(const verible::Symbol& syntax);
  
  // Driver/reader analysis
  void AnalyzeDrivers();
  void AnalyzeReaders();
  void ComputeFanout();
  
  // Dependency analysis helpers
  void BuildDependencyChains();
  std::vector<std::string> ComputeTransitiveClosure(const std::string& node);
  
  // Multi-driver detection
  void CheckMultiDriverConflicts();
  bool IsValidMultiDriver(const DataFlowNode& node);
  
  // Constant propagation
  void PropagateConstantsRecursive(DataFlowNode& node);
  bool IsConstantExpression(const verible::Symbol& expr);
  
  // Error reporting
  void AddError(const std::string& message, const verible::Symbol* origin);
  void AddWarning(const std::string& message, const verible::Symbol* origin);
  
  // Member variables
  const SymbolTable& symbol_table_;
  const VerilogProject& project_;
  DataFlowGraph graph_;
  std::vector<std::string> errors_;
  std::vector<std::string> warnings_;
};

}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_DATA_FLOW_ANALYZER_H_

