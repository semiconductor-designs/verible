# Week 10: DataFlowAnalyzer - Detailed Design Document

**Component**: `DataFlowAnalyzer`  
**Week**: 10 (Days 46-50)  
**Status**: 🎨 Design Phase  
**Target**: Data flow tracking and dependency analysis for SystemVerilog

---

## 🎯 **Overview**

The `DataFlowAnalyzer` tracks how data flows through SystemVerilog designs, building a comprehensive graph of driver-driven relationships, analyzing dependencies, and detecting issues like multi-driver conflicts.

### **Key Capabilities**

1. **Driver Tracking**: Identify what drives each signal/variable
2. **Reader Tracking**: Track where each signal is read
3. **Dependency Analysis**: Build transitive dependency chains
4. **Assignment Analysis**: Understand blocking vs. non-blocking assignments
5. **Multi-Driver Detection**: Find signals with multiple drivers (potential conflicts)
6. **Constant Propagation**: Identify compile-time constants
7. **Port Data Flow**: Track data flow through module ports
8. **Cross-Module Flow**: Understand data flow across module boundaries

---

## 📊 **Core Data Structures**

### **1. DataFlowNode**

Represents a signal, variable, port, or parameter in the design.

```cpp
struct DataFlowNode {
  // Identity
  std::string name;                          // Full hierarchical name
  std::string local_name;                    // Local name within scope
  
  // Source information
  const verible::Symbol* syntax_origin;      // CST node where declared
  const VerilogSourceFile* file;             // Source file
  int line_number;                           // Line number
  
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
  bool is_constant;                          // Compile-time constant
  bool is_parameter;                         // Is a parameter
  bool has_multi_driver;                     // Multiple drivers (conflict)
  bool is_port;                              // Is a port
  bool is_read;                              // Ever read from
  bool is_written;                           // Ever written to
  int fanout;                                // Number of readers
  int driver_count;                          // Number of drivers
  
  // Scope information
  std::string scope;                         // Hierarchical scope
  const SymbolTableNode* symbol_node;        // Symbol table node
};
```

### **2. DataFlowEdge**

Represents a data flow connection between two nodes.

```cpp
struct DataFlowEdge {
  // Endpoints
  DataFlowNode* source;                      // Source node (driver)
  DataFlowNode* target;                      // Target node (driven)
  
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
  bool is_conditional;                       // Inside if/case
  std::string condition;                     // Condition expression (if any)
  
  // Properties
  bool is_complete_driver;                   // Drives all bits
  bool is_partial_driver;                    // Drives some bits
};
```

### **3. DataFlowGraph**

The complete data flow graph for a design.

```cpp
class DataFlowGraph {
 public:
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
};
```

---

## 🏗️ **Class API: DataFlowAnalyzer**

```cpp
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
```

---

## 🔍 **Algorithm Details**

### **1. Building the Data Flow Graph**

```
Algorithm: BuildDataFlowGraph()
─────────────────────────────────────
1. TraverseSymbolTable(root, "")
   - For each symbol table node:
     a. Extract signals (wire, reg, logic)
     b. Extract variables (local to functions/tasks)
     c. Extract ports (input, output, inout)
     d. Extract parameters
     e. Create DataFlowNode for each
   
2. ExtractAssignments(root)
   - For each module:
     a. Find all blocking assignments (=)
     b. Find all non-blocking assignments (<=)
     c. Find all continuous assignments (assign)
     d. Find all port connections
     e. Create DataFlowEdge for each
   
3. AnalyzeDrivers()
   - For each DataFlowEdge:
     a. Add edge.source to edge.target.drivers
     b. Increment edge.target.driver_count
   
4. AnalyzeReaders()
   - For each DataFlowEdge:
     a. Add edge.target to edge.source.readers
     b. Set edge.source.is_read = true
   
5. ComputeFanout()
   - For each DataFlowNode:
     a. node.fanout = node.readers.size()
```

### **2. Multi-Driver Detection**

```
Algorithm: DetectMultiDrivers()
────────────────────────────────
For each DataFlowNode node in graph.nodes:
  1. If node.driver_count > 1:
     a. Check if all drivers are in different always blocks
     b. Check if drivers have mutually exclusive conditions
     c. If not mutually exclusive:
        - Report error: "Multi-driver conflict"
        - Add to graph.multi_driver_nodes
     d. If mutually exclusive:
        - Report warning: "Multiple conditional drivers"
  
  2. Special case: inout ports
     - Multiple drivers allowed for bidirectional ports
  
  3. Special case: tri-state logic
     - Multiple drivers allowed if high-impedance (z) is used
```

### **3. Dependency Chain Analysis**

```
Algorithm: BuildDependencyChains()
───────────────────────────────────
For each DataFlowNode node in graph.nodes:
  1. dependencies[node.name] = ComputeTransitiveClosure(node.name)

Algorithm: ComputeTransitiveClosure(node_name)
───────────────────────────────────────────────
Input: node_name (string)
Output: List of all nodes that node_name transitively depends on

1. result = []
2. visited = set()
3. queue = [node_name]

4. While queue is not empty:
   a. current = queue.pop()
   b. If current in visited: continue
   c. visited.add(current)
   d. result.append(current)
   
   e. current_node = graph.FindNode(current)
   f. For each driver in current_node.drivers:
      - If driver.name not in visited:
        queue.append(driver.name)

5. Return result
```

### **4. Constant Propagation**

```
Algorithm: PropagateConstants()
────────────────────────────────
1. Mark all parameters and localparams as constants
   - For each DataFlowNode with type == kParameter:
     node.is_constant = true

2. Propagate through assignments
   - For each DataFlowEdge edge in graph.edges:
     a. If edge.source.is_constant:
        b. If edge.assignment is direct (no operations):
           edge.target.is_constant = true
        c. If edge.assignment uses only constants:
           edge.target.is_constant = true

3. Iterate until fixed point
   - Repeat step 2 until no new constants are found
```

---

## 🧪 **Test Strategy**

### **Test Categories (20+ tests total)**

#### **1. Basic Data Flow (5 tests)**
- `SimpleAssignment`: `wire a; wire b; assign b = a;`
- `BlockingAssignment`: `always @(*) b = a;`
- `NonBlockingAssignment`: `always @(posedge clk) b <= a;`
- `ChainedAssignments`: `a -> b -> c -> d`
- `MultipleReaders`: `a` drives `b`, `c`, `d`

#### **2. Multi-Driver Detection (4 tests)**
- `MultiDriverConflict`: Two always blocks drive same signal
- `MutuallyExclusiveDrivers`: `if (sel) a = b; else a = c;`
- `MultiDriverError`: Conflicting drivers detected
- `BidirectionalPort`: `inout` port with multiple drivers (allowed)

#### **3. Dependency Analysis (4 tests)**
- `SimpleDependency`: `c = a + b` -> c depends on a, b
- `TransitiveDependency`: `d = c; c = b; b = a;` -> d depends on a, b, c
- `CircularDependency`: `a = b; b = a;` (combinational loop)
- `CrossModuleDependency`: Port connections

#### **4. Constant Propagation (3 tests)**
- `ParameterConstant`: Parameters are constants
- `ConstantAssignment`: `wire a = 1'b0;` -> a is constant
- `ConstantPropagation`: `localparam A = 5; wire b = A;` -> b is constant

#### **5. Port Data Flow (2 tests)**
- `InputToOutput`: Data flow from input port to output port
- `PortConnection`: Module instantiation port connections

#### **6. Edge Cases (2 tests)**
- `EmptyModule`: Module with no signals
- `UnconnectedSignals`: Signals with no drivers or readers

### **Test Data Files**

Create `verible/verilog/analysis/testdata/dataflow/` with:

1. `simple_assignment.sv` - Basic assignments
2. `blocking_nonblocking.sv` - Different assignment types
3. `multi_driver_conflict.sv` - Multi-driver errors
4. `conditional_drivers.sv` - Mutually exclusive drivers
5. `dependency_chain.sv` - Transitive dependencies
6. `circular_dependency.sv` - Combinational loops
7. `constant_propagation.sv` - Constant analysis
8. `port_dataflow.sv` - Port connections
9. `cross_module_flow.sv` - Data flow across modules
10. `complex_dataflow.sv` - Real-world scenario
11. `empty_module.sv` - Edge case
12. `unconnected_signals.sv` - Edge case

---

## 🔗 **Integration Points**

### **With Existing Components**

#### **1. SymbolTable (Phase 1)**
- **Use**: Traverse symbol table to find signals, variables, ports
- **Method**: `TraverseSymbolTable(symbol_table_.Root(), "")`
- **Data**: Extract `kDataNetVariableInstance`, `kModule`, `kPort`

#### **2. VerilogProject (Phase 1)**
- **Use**: Access source files for error reporting
- **Method**: `project_.GetTextStructure(file)`
- **Data**: File paths, line numbers

#### **3. HierarchicalTypeChecker (Phase 2 Week 9)**
- **Use**: Understand type relationships for data flow
- **Method**: `type_checker.GetTypeHierarchy()`
- **Data**: Type information for signals

#### **4. PortConnectionValidator (Phase 2 Week 7)**
- **Use**: Validate data flow through port connections
- **Method**: Share port connection information
- **Data**: Port mappings, connection validity

---

## 📈 **Performance Considerations**

### **Time Complexity**

- **Building graph**: O(N) where N = number of nodes + edges
- **Multi-driver detection**: O(N) single pass through nodes
- **Dependency chains**: O(N × M) where M = avg dependency depth
- **Constant propagation**: O(N × K) where K = iterations (usually <5)

### **Space Complexity**

- **Nodes**: O(N) where N = signals + variables + ports + parameters
- **Edges**: O(E) where E = assignments + port connections
- **Dependency map**: O(N × D) where D = avg dependencies per node

### **Expected Performance**

For a typical 10,000 line SystemVerilog module:
- ~1,000 signals/variables
- ~5,000 assignments
- Build time: <1 second
- Memory: <10 MB

---

## ⚠️ **Known Limitations**

### **Version 1.0 Limitations**

1. **SystemVerilog Features Not Supported**:
   - Packed arrays (partial bit-select analysis)
   - Unpacked arrays (array index tracking)
   - Structs (field-level data flow)
   - Classes (object data flow)
   - Dynamic arrays (runtime allocation)

2. **Advanced Analysis Not Included**:
   - Timing analysis (clock domain crossing)
   - Path analysis (critical paths)
   - Coverage analysis (signal toggle coverage)

3. **Parser Limitations**:
   - Depends on Verible parser capabilities
   - Some SystemVerilog 2017 features may not be supported

### **Future Enhancements**

- Array element tracking
- Struct field tracking
- Class member tracking
- Clock domain analysis
- Path delay analysis
- Coverage metrics

---

## 🎯 **Success Criteria**

### **Week 10 Complete When:**

✅ `DataFlowAnalyzer` class implemented (400+ lines)  
✅ All data structures defined (`DataFlowNode`, `DataFlowEdge`, `DataFlowGraph`)  
✅ 20+ tests written  
✅ 16+ tests passing (80%+)  
✅ Multi-driver detection working  
✅ Dependency chain analysis working  
✅ Constant propagation working  
✅ Integration with `SymbolTable` working  
✅ Comprehensive documentation complete  
✅ Code committed to Git  

---

## 📋 **Implementation Checklist**

### **Day 47: Test Infrastructure & Header**
- [ ] Create `testdata/dataflow/` directory
- [ ] Create README.md for test data
- [ ] Create 12 test .sv files
- [ ] Create `data-flow-analyzer.h`
- [ ] Define all data structures
- [ ] Update BUILD file
- [ ] Commit

### **Day 48: Core Implementation Part 1**
- [ ] Create `data-flow-analyzer.cc`
- [ ] Implement constructor
- [ ] Implement `TraverseSymbolTable()`
- [ ] Implement `ExtractSignals()`
- [ ] Implement `ExtractAssignments()`
- [ ] Implement `AnalyzeDrivers()`
- [ ] Compile successfully
- [ ] Commit

### **Day 49: Core Implementation Part 2 & Tests**
- [ ] Implement `AnalyzeReaders()`
- [ ] Implement `ComputeFanout()`
- [ ] Implement `DetectMultiDrivers()`
- [ ] Implement `BuildDependencyChains()`
- [ ] Implement `PropagateConstants()`
- [ ] Create `data-flow-analyzer_test.cc`
- [ ] Write 20+ tests
- [ ] Compile all tests
- [ ] Commit

### **Day 50: Testing & Documentation**
- [ ] Run all tests
- [ ] Debug failing tests
- [ ] Target: 16+/20 passing (80%+)
- [ ] Create WEEK10_DATAFLOW_COMPLETE.md
- [ ] Update Phase 3 progress
- [ ] Final commit
- [ ] **Week 10 Complete!**

---

## 🚀 **Ready to Implement**

This design provides:
- ✅ Complete API specification
- ✅ Detailed data structures
- ✅ Algorithm descriptions
- ✅ Test strategy
- ✅ Integration plan
- ✅ Performance analysis
- ✅ Success criteria

**Next Step**: Day 47 - Create test infrastructure and header file!

---

**Status**: ✅ Design Complete  
**Next**: Day 47 implementation  
**Target**: 80%+ test pass rate by Day 50  
**Philosophy**: No hurry. Perfection! TDD.

