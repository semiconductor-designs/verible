# Week 12: CallGraphEnhancer - Detailed Design Document

**Component**: `CallGraphEnhancer`  
**Week**: 12 (Days 56-60)  
**Status**: 🎨 Design Phase  
**Target**: Comprehensive call graph analysis for SystemVerilog

---

## 🎯 **Overview**

The `CallGraphEnhancer` builds upon the existing `CallGraph` component to provide enhanced call graph analysis with recursion detection, call chain analysis, and cross-module tracking. It provides semantic-level understanding of function and task calls throughout a SystemVerilog design.

### **Key Capabilities**

1. **Call Graph Construction**: Build complete function/task call graphs
2. **Recursion Detection**: Detect direct and indirect recursion
3. **Call Chain Analysis**: Track complete call chains (who calls whom)
4. **Unreachable Function Detection**: Find functions that are never called
5. **Entry Point Identification**: Identify entry points (top-level functions)
6. **Cross-Module Calls**: Track calls across module boundaries
7. **Virtual Function Handling**: Handle polymorphic calls
8. **DPI Function Detection**: Identify DPI functions (may be called from C/C++)
9. **Call Depth Analysis**: Compute maximum call depth
10. **Integration with Existing CallGraph**: Enhance existing infrastructure

---

## 📊 **Core Data Structures**

### **1. CallGraphNode**

Represents a function or task in the call graph.

```cpp
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
    kDPIFunction,       // DPI function (may be called externally)
    kSystemFunction,    // System function ($display, $random, etc.)
    kVirtualFunction    // Virtual function (polymorphic)
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
  int recursive_depth;                       // Recursion depth (if recursive)
  
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
```

### **2. CallGraphEdge**

Represents a call relationship between functions/tasks.

```cpp
struct CallGraphEdge {
  CallGraphNode* caller;                     // Calling function
  CallGraphNode* callee;                     // Called function
  const verible::Symbol* call_site;          // Where the call occurs
  
  // Call type
  enum CallType {
    kDirect,            // Direct call (func())
    kIndirect,          // Indirect (function pointer, virtual)
    kRecursive          // Recursive call (part of cycle)
  } call_type;
  
  // Constructor
  CallGraphEdge()
      : caller(nullptr),
        callee(nullptr),
        call_site(nullptr),
        call_type(kDirect) {}
};
```

### **3. RecursionCycle**

Represents a detected recursion cycle.

```cpp
struct RecursionCycle {
  std::vector<CallGraphNode*> cycle_nodes;   // Nodes in the cycle
  std::vector<CallGraphEdge*> cycle_edges;   // Edges in the cycle
  
  enum CycleType {
    kDirect,            // f() calls f()
    kIndirect           // f() -> g() -> f()
  } cycle_type;
  
  int cycle_length;                          // Number of nodes in cycle
  CallGraphNode* entry_node;                 // Where cycle starts
  
  // Constructor
  RecursionCycle()
      : cycle_type(kDirect),
        cycle_length(0),
        entry_node(nullptr) {}
};
```

### **4. CallGraphStatistics**

Tracks detailed call graph statistics.

```cpp
struct CallGraphStatistics {
  // Counts
  int total_functions;
  int total_tasks;
  int total_nodes;                           // functions + tasks
  int total_edges;                           // call relationships
  
  int entry_points;                          // Functions with no callers
  int unreachable_functions;                 // Functions never called
  int recursive_functions;                   // Functions in cycles
  int dpi_functions;                         // DPI functions
  int virtual_functions;                     // Virtual functions
  
  int direct_calls;                          // Direct function calls
  int indirect_calls;                        // Indirect calls
  
  int recursion_cycles;                      // Number of cycles detected
  int direct_recursion;                      // f() -> f()
  int indirect_recursion;                    // f() -> g() -> f()
  
  int max_call_depth;                        // Maximum call chain depth
  float avg_call_depth;                      // Average call depth
  
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
```

---

## 🏗️ **Class API: CallGraphEnhancer**

```cpp
class CallGraphEnhancer {
 public:
  // Constructor
  CallGraphEnhancer(const SymbolTable& symbol_table,
                    const VerilogProject& project);
  
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
  std::vector<CallGraphNode*> GetAllNodes() const { return nodes_; }
  std::vector<CallGraphEdge*> GetAllEdges() const { return edges_; }
  std::vector<CallGraphNode*> GetEntryPoints() const;
  std::vector<CallGraphNode*> GetUnreachableFunctions() const;
  std::vector<RecursionCycle> GetRecursionCycles() const { return recursion_cycles_; }
  CallGraphStatistics GetStatistics() const { return statistics_; }
  
  // Specific queries
  CallGraphNode* GetNode(const std::string& function_name) const;
  std::vector<CallGraphNode*> GetCallers(const std::string& function_name) const;
  std::vector<CallGraphNode*> GetCallees(const std::string& function_name) const;
  std::vector<CallGraphNode*> GetCallChain(const std::string& from, const std::string& to) const;
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
  CallGraphNode* CreateNode(const std::string& name, CallGraphNode::NodeType type);
  CallGraphNode* FindNode(const std::string& name) const;
  void AddNode(CallGraphNode* node);
  
  // Edge management
  CallGraphEdge* CreateEdge(CallGraphNode* caller, CallGraphNode* callee,
                            const verible::Symbol* call_site);
  void AddEdge(CallGraphEdge* edge);
  
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
                          std::vector<CallGraphNode*>& visited,
                          std::vector<CallGraphNode*>& rec_stack);
  bool IsInRecursionStack(CallGraphNode* node, 
                          const std::vector<CallGraphNode*>& rec_stack);
  void MarkRecursiveCycle(const std::vector<CallGraphNode*>& cycle);
  
  // Depth computation
  void ComputeDepthBFS(CallGraphNode* entry_point);
  int ComputeMaxDepth(CallGraphNode* node, std::set<CallGraphNode*>& visited);
  
  // Entry point detection
  bool IsEntryPoint(CallGraphNode* node);
  
  // Statistics
  void ComputeStatistics();
  void UpdateStatistics();
  
  // Warning/error reporting
  void AddWarning(const std::string& message);
  void AddError(const std::string& message);
  
  // Member variables
  const SymbolTable& symbol_table_;
  const VerilogProject& project_;
  std::vector<CallGraphNode*> nodes_;
  std::vector<CallGraphEdge*> edges_;
  std::map<std::string, CallGraphNode*> name_to_node_;
  std::vector<RecursionCycle> recursion_cycles_;
  CallGraphStatistics statistics_;
  std::vector<std::string> warnings_;
  std::vector<std::string> errors_;
  
  // Configuration
  bool detect_dpi_;
  int max_call_depth_;
};
```

---

## 🔍 **Algorithm Details**

### **1. Building Call Graph**

```
Algorithm: BuildEnhancedCallGraph()
─────────────────────────────────────
1. Extract all functions:
   - Traverse symbol table
   - Find kFunction metatype nodes
   - Create CallGraphNode for each
   - Add to nodes_ vector

2. Extract all tasks:
   - Find kTask metatype nodes
   - Create CallGraphNode for each
   - Add to nodes_ vector

3. Extract call sites:
   - For each function node:
     a. Get function body from CST
     b. Search for function call expressions
     c. Extract called function name
     d. Store call site locations

4. Build call edges:
   - For each call site:
     a. Get caller node
     b. Get callee node (lookup by name)
     c. Create CallGraphEdge
     d. Add to caller.callees
     e. Add to callee.callers
     f. Add to edges_ vector

5. Detect recursion (DFS-based)
6. Compute call depths (BFS-based)
7. Identify entry points
8. Find unreachable functions
9. Compute statistics
```

### **2. Recursion Detection (DFS with Stack)**

```
Algorithm: DetectRecursion()
─────────────────────────────
1. Initialize:
   - visited = empty set
   - rec_stack = empty stack

2. For each node in nodes_:
   if node not in visited:
     DetectRecursionDFS(node, visited, rec_stack)

DetectRecursionDFS(node, visited, rec_stack):
1. Add node to visited
2. Add node to rec_stack

3. For each callee in node.callees:
   a. If callee not in visited:
      - DetectRecursionDFS(callee, visited, rec_stack)
   b. Else if callee in rec_stack:
      - Recursion detected!
      - Extract cycle from rec_stack
      - Create RecursionCycle
      - Mark all nodes in cycle as is_recursive = true
      - Add to recursion_cycles_

4. Remove node from rec_stack
```

### **3. Call Depth Computation (BFS)**

```
Algorithm: ComputeCallDepths()
───────────────────────────────
1. Find all entry points (nodes with no callers)

2. For each entry point:
   - Set depth = 0
   - BFS traversal:
     a. Enqueue entry point
     b. While queue not empty:
        - Dequeue node
        - For each callee:
          * callee.depth = max(callee.depth, node.depth + 1)
          * Enqueue callee

3. Compute max_call_depth:
   - Max of all node depths

4. Compute avg_call_depth:
   - Average of all node depths
```

### **4. Unreachable Function Detection**

```
Algorithm: FindUnreachableFunctions()
──────────────────────────────────────
1. For each node in nodes_:
   if node.callers.size() == 0:
     if node is NOT entry point:
       if node is NOT DPI function:
         node.is_unreachable = true
         unreachable_functions++
```

---

## 🧪 **Test Strategy**

### **Test Categories (25+ tests total)**

#### **1. Call Graph Construction (6 tests)**
- `EmptyModule`: Module with no functions
- `SingleFunction`: One function, no calls
- `SimpleFunctionCall`: Function A calls Function B
- `ChainedCalls`: A -> B -> C
- `MultipleCalls`: A calls B and C
- `TaskCalls`: Task call graph

#### **2. Recursion Detection (6 tests)**
- `DirectRecursion`: f() calls f()
- `IndirectRecursion`: f() -> g() -> f()
- `LongCycle`: f() -> g() -> h() -> f()
- `MultipleCycles`: Multiple independent cycles
- `NoRecursion`: Acyclic graph
- `RecursiveDepth`: Compute recursion depth

#### **3. Call Depth Analysis (4 tests)**
- `LinearDepth`: A -> B -> C (depth = 2)
- `BranchingDepth`: Multiple paths, different depths
- `MaxDepthComputation`: Verify max depth
- `EntryPointDepth`: Entry points have depth 0

#### **4. Entry Point Detection (3 tests)**
- `SingleEntryPoint`: One top-level function
- `MultipleEntryPoints`: Several top-level functions
- `NoEntryPoints`: All functions call each other

#### **5. Unreachable Function Detection (3 tests)**
- `UnreachableFunction`: Function never called
- `AllReachable`: All functions reachable from entry
- `PartiallyReachable`: Some reachable, some not

#### **6. Query Methods (4 tests)**
- `GetCallersQuery`: Get all callers of a function
- `GetCalleesQuery`: Get all callees of a function
- `GetCallChain`: Find path from A to B
- `GetStatistics`: Verify statistics computation

#### **7. Edge Cases (4 tests)**
- `SelfCall`: Function calls itself
- `MutualRecursion`: A calls B, B calls A
- `LargeCallGraph`: 100+ functions
- `CrossModuleCalls`: Calls across modules

---

## 🔗 **Integration Points**

### **With Existing CallGraph**

**Strategy**: Enhance, not replace
- **Use**: Existing `CallGraph` class as foundation
- **Extend**: Add enhanced analysis methods
- **API**: Maintain compatibility
- **Migration**: Gradual enhancement

### **With SymbolTable**

**Use**: Access to all function/task definitions
- **Methods**: Traverse symbol table for kFunction, kTask
- **Data**: Symbol names, syntax origins, file origins

### **With CST (Concrete Syntax Tree)**

**Use**: Extract call sites from function bodies
- **Methods**: Search for function call expressions
- **Patterns**: Use VerilogMatchers to find calls

### **With EnhancedUnusedDetector (Week 11)**

**Synergy**: Share unreachable function detection
- **CallGraphEnhancer**: Finds functions never called via graph
- **UnusedDetector**: Can use this information

---

## 📈 **Performance Considerations**

### **Time Complexity**

- **ExtractFunctions()**: O(N) where N = nodes in symbol table
- **ExtractCallSites()**: O(F × B) where F = functions, B = body size
- **BuildCallEdges()**: O(C) where C = call sites
- **DetectRecursion()**: O(V + E) where V = nodes, E = edges (DFS)
- **ComputeCallDepths()**: O(V + E) (BFS)
- **Overall**: O(N + F × B + V + E) ≈ O(F × B) typically

### **Space Complexity**

- **nodes_**: O(F + T) where F = functions, T = tasks
- **edges_**: O(C) where C = call sites
- **recursion_cycles_**: O(R × L) where R = cycles, L = avg cycle length
- **Overall**: O(F + C + R × L)

### **Expected Performance**

For a typical 10,000 line SystemVerilog design:
- ~100 functions/tasks
- ~500 call sites
- Analysis time: <3 seconds
- Memory: <10 MB

---

## ⚠️ **Known Limitations**

### **Version 1.0 Limitations**

1. **Indirect Calls**:
   - Function pointers not fully supported
   - Virtual function calls may be missed
   - Polymorphic calls need enhancement

2. **Cross-Module Calls**:
   - Basic support only
   - Parameter-dependent calls may be missed

3. **DPI Functions**:
   - Detection based on keywords/patterns
   - May miss some DPI functions

4. **System Functions**:
   - $display, $random, etc. treated specially
   - Not all system functions catalogued

### **Mitigation Strategies**

1. **Conservative Analysis**:
   - Mark uncertain calls as indirect
   - Flag potential missed calls as warnings

2. **User Configuration**:
   - Allow marking functions as DPI
   - Custom entry point specification

3. **Heuristics**:
   - Function name patterns
   - Annotation comments (// @dpi, // @entry)

---

## 🎯 **Success Criteria**

### **Week 12 Complete When:**

✅ `CallGraphEnhancer` class implemented (500+ lines)  
✅ All data structures defined (4 structs)  
✅ 25+ tests written  
✅ 22+ tests passing (88%+)  
✅ Call graph construction working  
✅ Recursion detection working (direct & indirect)  
✅ Call depth computation working  
✅ Entry point identification working  
✅ Unreachable function detection working  
✅ Query methods working  
✅ Comprehensive documentation complete  
✅ Code committed to Git  

---

## 📋 **Implementation Checklist**

### **Day 56: Design & Test Infrastructure**
- [x] Create PHASE3_WEEK12_CALLGRAPH_DESIGN.md
- [ ] Create `testdata/callgraph/` directory
- [ ] Create README.md for test data
- [ ] Create 12+ test .sv files
- [ ] Create `call-graph-enhancer.h`
- [ ] Define all data structures
- [ ] Update BUILD file
- [ ] Commit

### **Day 57: Core Implementation Part 1**
- [ ] Create `call-graph-enhancer.cc`
- [ ] Implement constructor
- [ ] Implement ExtractFunctions()
- [ ] Implement ExtractTasks()
- [ ] Implement ExtractCallSites()
- [ ] Implement BuildCallEdges()
- [ ] Compile successfully
- [ ] Commit

### **Day 58: Core Implementation Part 2**
- [ ] Implement DetectRecursion() (DFS)
- [ ] Implement ComputeCallDepths() (BFS)
- [ ] Implement IdentifyEntryPoints()
- [ ] Implement FindUnreachableFunctions()
- [ ] Implement query methods
- [ ] Compile successfully
- [ ] Commit

### **Day 59: Test Framework**
- [ ] Create `call-graph-enhancer_test.cc`
- [ ] Write 25+ tests
- [ ] Implement test fixture
- [ ] Compile all tests
- [ ] Run tests (target: 22+/25 passing = 88%+)
- [ ] Commit

### **Day 60: Testing, Integration & Documentation**
- [ ] Debug failing tests
- [ ] Target: 22+/25 passing (88%+)
- [ ] Create WEEK12_CALLGRAPH_COMPLETE.md
- [ ] Create PHASE3_COMPLETE.md (final summary)
- [ ] Update Phase 3 progress
- [ ] Final commit
- [ ] **Week 12 Complete!**
- [ ] **Phase 3 Complete!**

---

## 🚀 **Ready to Implement**

This design provides:
- ✅ Complete API specification
- ✅ Detailed data structures (4 structs)
- ✅ Algorithm descriptions (DFS, BFS)
- ✅ Test strategy (25+ tests)
- ✅ Integration plan
- ✅ Performance analysis
- ✅ Success criteria

**Next Step**: Create test infrastructure and header file (Day 56 continues)!

---

**Status**: ✅ Design Complete  
**Next**: Test infrastructure creation  
**Target**: 88%+ test pass rate by Day 60  
**Philosophy**: No hurry. Perfection! TDD.

