# Week 11: EnhancedUnusedDetector - Detailed Design Document

**Component**: `EnhancedUnusedDetector`  
**Week**: 11 (Days 51-55)  
**Status**: 🎨 Design Phase  
**Target**: Advanced unused code detection for SystemVerilog

---

## 🎯 **Overview**

The `EnhancedUnusedDetector` builds upon the `DataFlowAnalyzer` to provide semantic-level unused code detection. It goes beyond simple "declared but not referenced" checks to understand actual data flow and usage patterns.

### **Key Capabilities**

1. **Unused Signal Detection**: Signals that are never read (write-only or completely unused)
2. **Write-Only Detection**: Signals written but never read
3. **Read-Only Detection**: Signals read but never written (undriven, potentially errors)
4. **Unused Variable Detection**: Local variables that are never used
5. **Unused Function/Task Detection**: Functions/tasks that are never called
6. **Unused Module Detection**: Modules that are never instantiated
7. **Dead Code Detection**: Unreachable code paths
8. **Integration with DataFlowAnalyzer**: Leverages existing data flow information

---

## 📊 **Core Data Structures**

### **1. UnusedEntity**

Represents an entity detected as unused.

```cpp
struct UnusedEntity {
  // Identity
  std::string name;                          // Entity name
  std::string fully_qualified_name;          // Full hierarchical name
  
  // Source information
  const verible::Symbol* syntax_origin;      // CST node where declared
  const VerilogSourceFile* file;             // Source file
  int line_number;                           // Line number
  
  // Entity type
  enum EntityType {
    kSignal,            // Wire, reg, logic
    kVariable,          // Local variable
    kFunction,          // Function
    kTask,              // Task
    kModule,            // Module definition
    kPort,              // Module port
    kParameter,         // Parameter
    kDeadCode           // Unreachable code block
  } type;
  
  // Reason for being unused
  enum UnusedReason {
    kNeverRead,         // Written but never read
    kNeverWritten,      // Read but never written (undriven)
    kNeverReferenced,   // Never referenced at all
    kUnreachable,       // Control flow never reaches
    kWriteOnly,         // Only written, never read
    kReadOnly           // Only read, never written
  } reason;
  
  // Additional context
  std::string explanation;                   // Human-readable reason
  bool is_port;                              // Is this a port (may be intentionally unused)
  bool is_output;                            // Is this an output (write-only may be ok)
  bool is_input;                             // Is this an input (read-only may be ok)
  
  // Constructor
  UnusedEntity()
      : syntax_origin(nullptr),
        file(nullptr),
        line_number(0),
        type(kSignal),
        reason(kNeverReferenced),
        is_port(false),
        is_output(false),
        is_input(false) {}
};
```

### **2. UsageStatistics**

Tracks detailed usage statistics for debugging and reporting.

```cpp
struct UsageStatistics {
  // Counts
  int total_signals;
  int unused_signals;
  int write_only_signals;
  int read_only_signals;
  
  int total_variables;
  int unused_variables;
  
  int total_functions;
  int unused_functions;
  
  int total_tasks;
  int unused_tasks;
  
  int total_modules;
  int unused_modules;
  
  int dead_code_blocks;
  
  // Percentages
  float unused_signal_percentage;
  float unused_function_percentage;
  
  // Constructor
  UsageStatistics()
      : total_signals(0),
        unused_signals(0),
        write_only_signals(0),
        read_only_signals(0),
        total_variables(0),
        unused_variables(0),
        total_functions(0),
        unused_functions(0),
        total_tasks(0),
        unused_tasks(0),
        total_modules(0),
        unused_modules(0),
        dead_code_blocks(0),
        unused_signal_percentage(0.0f),
        unused_function_percentage(0.0f) {}
};
```

---

## 🏗️ **Class API: EnhancedUnusedDetector**

```cpp
class EnhancedUnusedDetector {
 public:
  // Constructor
  EnhancedUnusedDetector(const DataFlowAnalyzer& dataflow_analyzer,
                         const SymbolTable& symbol_table);
  
  // Main analysis entry point
  absl::Status AnalyzeUnusedEntities();
  
  // Specific analysis methods
  absl::Status FindUnusedSignals();
  absl::Status FindWriteOnlySignals();
  absl::Status FindReadOnlySignals();
  absl::Status FindUnusedVariables();
  absl::Status FindUnusedFunctions();
  absl::Status FindUnusedTasks();
  absl::Status FindUnusedModules();
  absl::Status AnalyzeDeadCode();
  
  // Query methods
  std::vector<UnusedEntity> GetUnusedEntities() const { return unused_entities_; }
  std::vector<UnusedEntity> GetUnusedSignals() const;
  std::vector<UnusedEntity> GetUnusedFunctions() const;
  UsageStatistics GetStatistics() const { return statistics_; }
  
  // Filtering and configuration
  void SetIgnorePorts(bool ignore) { ignore_ports_ = ignore; }
  void SetIgnoreOutputs(bool ignore) { ignore_outputs_ = ignore; }
  void SetIgnoreInputs(bool ignore) { ignore_inputs_ = ignore; }
  void AddIgnorePattern(const std::string& pattern);
  
  // Error/warning reporting
  std::vector<std::string> GetWarnings() const { return warnings_; }
  
 private:
  // Analysis helpers
  bool IsSignalUsed(const DataFlowNode& node);
  bool IsVariableUsed(const SymbolTableNode& node);
  bool IsFunctionCalled(const std::string& function_name);
  bool IsModuleInstantiated(const std::string& module_name);
  
  // Filtering helpers
  bool ShouldIgnore(const UnusedEntity& entity);
  bool MatchesIgnorePattern(const std::string& name);
  bool IsFalsePositive(const UnusedEntity& entity);
  
  // Port/direction detection
  bool IsPort(const DataFlowNode& node);
  bool IsOutput(const DataFlowNode& node);
  bool IsInput(const DataFlowNode& node);
  
  // Statistics computation
  void ComputeStatistics();
  void UpdateStatistics(const UnusedEntity& entity);
  
  // Warning reporting
  void AddWarning(const std::string& message, const verible::Symbol* origin);
  
  // Member variables
  const DataFlowAnalyzer& dataflow_analyzer_;
  const SymbolTable& symbol_table_;
  std::vector<UnusedEntity> unused_entities_;
  UsageStatistics statistics_;
  std::vector<std::string> warnings_;
  
  // Configuration
  bool ignore_ports_;
  bool ignore_outputs_;
  bool ignore_inputs_;
  std::vector<std::string> ignore_patterns_;
};
```

---

## 🔍 **Algorithm Details**

### **1. Finding Unused Signals**

```
Algorithm: FindUnusedSignals()
────────────────────────────────
1. Get all signals from DataFlowAnalyzer
2. For each signal node:
   a. Check if node.is_read == false
   b. Check if node.is_written == false
   c. If both false:
      - Mark as kNeverReferenced
      - Add to unused_entities_
   d. Else if !is_read && is_written:
      - Mark as kWriteOnly (kNeverRead)
      - Add to unused_entities_
   e. Else if is_read && !is_written:
      - Mark as kReadOnly (kNeverWritten)
      - Add to unused_entities_
      
3. Filter false positives:
   - Ports (if ignore_ports_ == true)
   - Outputs (write-only is OK if ignore_outputs_ == true)
   - Inputs (read-only is OK if ignore_inputs_ == true)
   - Pattern matches (ignore_patterns_)
   
4. Return status
```

### **2. Finding Unused Variables**

```
Algorithm: FindUnusedVariables()
─────────────────────────────────
1. Traverse symbol table for kDataNetVariableInstance
2. Filter for variables in function/task scopes
3. For each variable:
   a. Check if it appears in DataFlowGraph
   b. If not in graph:
      - Never referenced
      - Add to unused_entities_
   c. If in graph but !is_read && !is_written:
      - Never used
      - Add to unused_entities_
      
4. Return status
```

### **3. Finding Unused Functions/Tasks**

```
Algorithm: FindUnusedFunctions()
─────────────────────────────────
1. Traverse symbol table for kFunction/kTask
2. For each function/task:
   a. Check if function_name appears in any call expressions
   b. Search symbol table for function call syntax nodes
   c. If not found:
      - Function never called
      - Add to unused_entities_ (type=kFunction/kTask)
      
3. Special cases:
   - Entry point functions (e.g., "main", test functions)
   - DPI functions (may be called from C/C++)
   - Virtual functions (may be called polymorphically)
   
4. Return status
```

### **4. Finding Unused Modules**

```
Algorithm: FindUnusedModules()
───────────────────────────────
1. Get all module definitions from symbol table
2. For each module definition:
   a. Search for module instantiations
   b. Check symbol table for kModuleInstance with this type
   c. If no instantiations found:
      - Module never instantiated
      - Add to unused_entities_ (type=kModule)
      
3. Special cases:
   - Top-level modules (no parent, entry point)
   - Test bench modules
   - Modules in `ifdef blocks
   
4. Return status
```

### **5. Dead Code Analysis**

```
Algorithm: AnalyzeDeadCode()
─────────────────────────────
1. Analyze conditional statements:
   a. Find if/else with constant conditions
   b. If condition is always true:
      - Else branch is dead code
   c. If condition is always false:
      - If branch is dead code
      
2. Analyze case statements:
   a. Check for unreachable case items
   b. If a case value is impossible:
      - Mark case item as dead code
      
3. Analyze `ifdef blocks:
   a. Check for undefined macros
   b. If macro never defined:
      - `ifdef block is dead code
      
4. For each dead code block:
   - Add to unused_entities_ (type=kDeadCode)
   
5. Return status
```

---

## 🧪 **Test Strategy**

### **Test Categories (25+ tests total)**

#### **1. Unused Signal Detection (8 tests)**
- `CompletelyUnusedSignal`: Signal never read or written
- `WriteOnlySignal`: Signal written but never read
- `ReadOnlySignal`: Signal read but never written (undriven)
- `UsedSignal`: Signal both read and written (should NOT be flagged)
- `UnusedInternalSignal`: Internal signal not used
- `UnusedWireWithAssign`: Wire with continuous assign but no readers
- `ChainedUnusedSignals`: Multiple unused signals in a chain
- `PartiallyUsedBus`: Some bits used, some unused

#### **2. Unused Variable Detection (5 tests)**
- `CompletelyUnusedVariable`: Local variable never referenced
- `DeclaredButNotUsed`: Variable declared but not used
- `UsedVariable`: Variable properly used (should NOT be flagged)
- `UnusedFunctionParameter`: Function parameter not used
- `UnusedTaskVariable`: Task-local variable not used

#### **3. Unused Function/Task Detection (6 tests)**
- `UnusedFunction`: Function defined but never called
- `UnusedTask`: Task defined but never called
- `CalledFunction`: Function that is called (should NOT be flagged)
- `RecursiveFunction`: Function that calls itself (should NOT be flagged)
- `EntryPointFunction`: Main/entry function (should NOT be flagged)
- `VirtualFunction`: Virtual function (may not have direct calls)

#### **4. Unused Module Detection (3 tests)**
- `UnusedModule`: Module defined but never instantiated
- `InstantiatedModule`: Module with instances (should NOT be flagged)
- `TopLevelModule`: Top module (should NOT be flagged)

#### **5. Dead Code Detection (3 tests)**
- `DeadIfBranch`: If branch with constant false condition
- `DeadElseBranch`: Else branch with constant true condition
- `UnreachableCaseItem`: Case item that's impossible

#### **6. Filtering and False Positives (5 tests)**
- `IgnorePortSignals`: Ports should be ignorable
- `IgnoreOutputSignals`: Output ports can be write-only
- `IgnoreInputSignals`: Input ports can be read-only
- `IgnorePattern`: Pattern-based ignoring
- `FalsePositiveFiltering`: Common false positives filtered

### **Test Data Files**

Create `verible/verilog/analysis/testdata/unused/` with:

1. `unused_signals.sv` - Various unused signal scenarios
2. `write_only_signals.sv` - Signals only written
3. `read_only_signals.sv` - Signals only read (undriven)
4. `unused_variables.sv` - Local variable scenarios
5. `unused_functions.sv` - Function/task scenarios
6. `unused_modules.sv` - Module definition scenarios
7. `dead_code.sv` - Unreachable code scenarios
8. `false_positives.sv` - Common false positive cases
9. `mixed_unused.sv` - Complex real-world scenario
10. `ignore_patterns.sv` - Pattern matching test cases

---

## 🔗 **Integration Points**

### **With DataFlowAnalyzer (Week 10)**

**Primary Integration:**
- **Use**: Get data flow graph with driver/reader information
- **Method**: `dataflow_analyzer_.GetDataFlowGraph()`
- **Data**: 
  - `node.is_read` - Has this signal been read?
  - `node.is_written` - Has this signal been written?
  - `node.readers` - List of readers
  - `node.drivers` - List of drivers
  - `node.fanout` - Number of readers

**Benefits:**
- No need to re-analyze data flow
- Leverage existing driver/reader tracking
- Semantic-level unused detection (not just textual)

### **With SymbolTable (Phase 1)**

**Use**: Access symbol information
- **Method**: Traverse `symbol_table_` for functions, modules, variables
- **Data**: `SymbolMetaType`, syntax origin, file origin

### **With Existing UnusedDetector**

**Comparison:**
- **Old**: Simple "declared but not used" detection
- **New**: Semantic analysis with data flow understanding
- **Strategy**: EnhancedUnusedDetector can replace or augment existing detector

---

## 📈 **Performance Considerations**

### **Time Complexity**

- **FindUnusedSignals()**: O(N) where N = number of signals (single pass)
- **FindUnusedVariables()**: O(V) where V = number of variables
- **FindUnusedFunctions()**: O(F × C) where F = functions, C = call sites (can be optimized with call graph)
- **FindUnusedModules()**: O(M × I) where M = modules, I = instances
- **AnalyzeDeadCode()**: O(B) where B = blocks (linear scan)

### **Space Complexity**

- **unused_entities_**: O(U) where U = number of unused entities
- **statistics_**: O(1) constant space
- **ignore_patterns_**: O(P) where P = number of patterns

### **Expected Performance**

For a typical 10,000 line SystemVerilog design:
- ~1,000 signals
- ~100 functions/tasks
- ~50 modules
- Analysis time: <2 seconds
- Memory: <5 MB

---

## ⚠️ **Known Limitations**

### **Version 1.0 Limitations**

1. **Call Graph Dependency**:
   - Function call detection is basic (string matching)
   - No sophisticated call graph yet (Week 12)
   - May miss indirect calls (function pointers, polymorphism)

2. **Dead Code Analysis**:
   - Constant folding is limited
   - Complex expressions not evaluated
   - Preprocessor directives not fully analyzed

3. **False Positives**:
   - May flag intentionally unused ports
   - May flag debugging signals
   - May flag signals used in assertions/coverage

4. **Module Instantiation**:
   - Basic name matching
   - Parameter overrides not considered
   - Generate blocks may be missed

### **Mitigation Strategies**

1. **Configuration Options**:
   - `ignore_ports_` flag
   - `ignore_patterns_` list
   - Per-entity type filtering

2. **Heuristics**:
   - Names starting with `unused_` are ignored
   - Test modules are ignored
   - Top-level modules are ignored

3. **User Feedback**:
   - Clear explanations in warnings
   - Syntax location for easy verification
   - Statistics to understand scope

### **Future Enhancements**

- Integration with CallGraphEnhancer (Week 12)
- Preprocessor-aware analysis
- Assertion/coverage awareness
- Configuration file support
- Whitelist/blacklist management

---

## 🎯 **Success Criteria**

### **Week 11 Complete When:**

✅ `EnhancedUnusedDetector` class implemented (400+ lines)  
✅ All data structures defined (`UnusedEntity`, `UsageStatistics`)  
✅ 25+ tests written  
✅ 21+ tests passing (85%+)  
✅ Unused signal detection working  
✅ Write-only/read-only detection working  
✅ Unused variable detection working  
✅ Unused function detection working  
✅ False positive filtering working  
✅ Integration with `DataFlowAnalyzer` working  
✅ Comprehensive documentation complete  
✅ Code committed to Git  

---

## 📋 **Implementation Checklist**

### **Day 51: Design & Test Infrastructure**
- [x] Create PHASE3_WEEK11_UNUSED_DESIGN.md
- [ ] Create `testdata/unused/` directory
- [ ] Create README.md for test data
- [ ] Create 10 test .sv files
- [ ] Create `enhanced-unused-detector.h`
- [ ] Define all data structures
- [ ] Update BUILD file
- [ ] Commit

### **Day 52: Core Implementation Part 1**
- [ ] Create `enhanced-unused-detector.cc`
- [ ] Implement constructor
- [ ] Implement `AnalyzeUnusedEntities()`
- [ ] Implement `FindUnusedSignals()`
- [ ] Implement `FindWriteOnlySignals()`
- [ ] Implement `FindReadOnlySignals()`
- [ ] Compile successfully
- [ ] Commit

### **Day 53: Core Implementation Part 2**
- [ ] Implement `FindUnusedVariables()`
- [ ] Implement `FindUnusedFunctions()`
- [ ] Implement `FindUnusedTasks()`
- [ ] Implement `FindUnusedModules()`
- [ ] Implement `AnalyzeDeadCode()`
- [ ] Compile successfully
- [ ] Commit

### **Day 54: Test Framework**
- [ ] Create `enhanced-unused-detector_test.cc`
- [ ] Write 25+ tests
- [ ] Implement test fixture
- [ ] Compile all tests
- [ ] Run tests (target: 18+/25 passing = 72%+)
- [ ] Commit

### **Day 55: Testing & Documentation**
- [ ] Debug failing tests
- [ ] Target: 21+/25 passing (85%+)
- [ ] Create WEEK11_UNUSED_COMPLETE.md
- [ ] Update Phase 3 progress
- [ ] Final commit
- [ ] **Week 11 Complete!**

---

## 🚀 **Ready to Implement**

This design provides:
- ✅ Complete API specification
- ✅ Detailed data structures
- ✅ Algorithm descriptions
- ✅ Test strategy (25+ tests)
- ✅ Integration plan with DataFlowAnalyzer
- ✅ Performance analysis
- ✅ Success criteria

**Next Step**: Create test infrastructure and header file (Day 51 continues)!

---

**Status**: ✅ Design Complete  
**Next**: Test infrastructure creation  
**Target**: 85%+ test pass rate by Day 55  
**Philosophy**: No hurry. Perfection! TDD.

