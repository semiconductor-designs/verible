# Phase 2: Semantic Analysis Implementation Plan

**Timeline:** 6 weeks  
**Goal:** Build comprehensive semantic analysis on top of 100% parser  
**Approach:** Incremental TDD - each feature with tests

---

## 🎯 Overview

Now that we have **100% IEEE 1800-2017 parsing**, we can build semantic analysis that:
1. Understands what the code **means**, not just its syntax
2. Catches errors beyond parse errors
3. Enables advanced IDE features
4. Provides foundation for refactoring tools

---

## 📊 Architecture

```
Verible Parser (100% Complete)
    ↓
Concrete Syntax Tree (CST)
    ↓
┌─────────────────────────────────┐
│  Semantic Analysis Layer (NEW)  │
├─────────────────────────────────┤
│ 1. Symbol Table Builder         │
│ 2. Type System                   │
│ 3. Scope Analyzer                │
│ 4. Reference Resolver            │
│ 5. Type Checker                  │
│ 6. Unused Detection              │
│ 7. Call Graph Builder            │
└─────────────────────────────────┘
    ↓
Enhanced Tools (IDE, Linter, Refactoring)
```

---

## 🗓️ Week 1: Symbol Table Foundation

### Goal
Build infrastructure to collect and organize all symbols (modules, variables, functions, etc.)

### Tasks

#### 1.1 Design Symbol Table Structure (Days 1-2)
**File:** `verible/common/analysis/symbol-table.h`

```cpp
class Symbol {
 public:
  enum class Kind {
    kModule, kInterface, kClass, kFunction, kTask,
    kVariable, kNet, kPort, kParameter, kTypedef
  };
  
  SymbolInfo info_;
  Location declaration_location_;
  std::vector<Location> reference_locations_;
  Scope* parent_scope_;
};

class Scope {
 public:
  std::map<std::string, Symbol*> symbols_;
  Scope* parent_;
  std::vector<std::unique_ptr<Scope>> children_;
  
  Symbol* Lookup(const std::string& name);
  Symbol* LookupHierarchical(const std::string& path);
};

class SymbolTable {
 public:
  void Build(const verible::ConcreteSyntaxTree& cst);
  Symbol* Resolve(const std::string& name, const Scope* scope);
  std::vector<Symbol*> GetAllSymbols();
};
```

**Tests:** `verible/common/analysis/symbol-table_test.cc`
- Test symbol creation
- Test scope nesting
- Test name lookup
- Test hierarchical lookup

#### 1.2 CST Visitor for Symbol Collection (Days 3-4)
**File:** `verible/verilog/analysis/symbol-table-builder.h`

```cpp
class SymbolTableBuilder : public verible::TreeVisitorRecursive {
 public:
  void Visit(const verible::SyntaxTreeNode& node) override;
  SymbolTable GetSymbolTable() { return std::move(symbol_table_); }
  
 private:
  void HandleModuleDeclaration(const verible::SyntaxTreeNode& node);
  void HandleVariableDeclaration(const verible::SyntaxTreeNode& node);
  void HandleFunctionDeclaration(const verible::SyntaxTreeNode& node);
  // ... other handlers
  
  SymbolTable symbol_table_;
  Scope* current_scope_ = nullptr;
};
```

**Tests:** `verible/verilog/analysis/symbol-table-builder_test.cc`
- Test module symbol collection
- Test variable collection
- Test function collection
- Test nested scopes

#### 1.3 Integration Tests (Day 5)
**File:** `verible/verilog/analysis/symbol-table-integration_test.cc`

Test real SystemVerilog files:
```systemverilog
module top;
  logic [7:0] data;
  always_ff @(posedge clk) data <= new_data;
endmodule
```

Verify:
- All symbols found
- Correct scopes
- No duplicates

---

## 🗓️ Week 2: Type System

### Goal
Represent and track all SystemVerilog types

### Tasks

#### 2.1 Type Representation (Days 1-2)
**File:** `verible/verilog/analysis/type-system.h`

```cpp
class Type {
 public:
  enum class Kind {
    kLogic, kBit, kReg, kWire, kInteger, kReal,
    kStruct, kUnion, kEnum, kClass, kInterface,
    kArray, kQueue, kAssociativeArray,
    kString, kChandle, kVoid, kUnknown
  };
  
  Kind kind() const { return kind_; }
  int width() const { return width_; }
  bool is_signed() const { return is_signed_; }
  const std::vector<Dimension>& dimensions() const { return dimensions_; }
  
  bool IsCompatible(const Type& other) const;
  bool IsAssignableFrom(const Type& other) const;
};

class TypeRegistry {
 public:
  const Type* GetBuiltinType(Type::Kind kind);
  const Type* CreatePackedType(Type::Kind kind, int width, bool is_signed);
  const Type* CreateArrayType(const Type* element_type, const std::vector<Dimension>& dims);
  const Type* CreateStructType(const std::vector<StructMember>& members);
};
```

**Tests:** `verible/verilog/analysis/type-system_test.cc`
- Test type compatibility
- Test assignment compatibility
- Test packed vs unpacked
- Test struct/union types

#### 2.2 Type Inference from CST (Days 3-4)
**File:** `verible/verilog/analysis/type-inference.h`

```cpp
class TypeInference {
 public:
  const Type* InferFromDeclaration(const verible::SyntaxTreeNode& decl);
  const Type* InferFromExpression(const verible::SyntaxTreeNode& expr);
  
 private:
  const Type* InferBinaryOp(const verible::SyntaxTreeNode& op, 
                            const Type* left, const Type* right);
  const Type* InferFunctionCall(const verible::SyntaxTreeNode& call);
  
  TypeRegistry* registry_;
  SymbolTable* symbols_;
};
```

**Tests:** `verible/verilog/analysis/type-inference_test.cc`
- Test variable type inference
- Test expression type inference
- Test function return type
- Test complex expressions

#### 2.3 Type Annotation (Day 5)
Attach types to symbols in symbol table

**Tests:** Full integration with symbol table

---

## 🗓️ Week 3: Reference Resolution

### Goal
Connect every use of a name to its declaration

### Tasks

#### 3.1 Reference Visitor (Days 1-2)
**File:** `verible/verilog/analysis/reference-resolver.h`

```cpp
class ReferenceResolver : public verible::TreeVisitorRecursive {
 public:
  void Visit(const verible::SyntaxTreeNode& node) override;
  
  struct Resolution {
    Symbol* declaration;
    std::vector<Location> references;
    bool is_ambiguous;
  };
  
  const std::map<std::string, Resolution>& GetResolutions() const;
  
 private:
  void HandleIdentifier(const verible::SyntaxTreeNode& node);
  void HandleHierarchicalIdentifier(const verible::SyntaxTreeNode& node);
  
  SymbolTable* symbol_table_;
  Scope* current_scope_;
};
```

**Tests:** `verible/verilog/analysis/reference-resolver_test.cc`
- Test simple reference resolution
- Test hierarchical references
- Test cross-module references
- Test ambiguous references

#### 3.2 Scope-Aware Resolution (Days 3-4)
Handle complex scoping:
- Module hierarchy
- Class inheritance
- Package imports
- Generate blocks

**Tests:** Complex scoping scenarios

#### 3.3 Unresolved Reference Detection (Day 5)
Report undeclared identifiers

**Tests:** Error detection tests

---

## 🗓️ Week 4: Type Checking

### Goal
Verify type correctness of operations and assignments

### Tasks

#### 4.1 Expression Type Checking (Days 1-2)
**File:** `verible/verilog/analysis/type-checker.h`

```cpp
class TypeChecker {
 public:
  struct TypeError {
    Location location;
    std::string message;
    const Type* expected;
    const Type* actual;
  };
  
  std::vector<TypeError> Check(const verible::ConcreteSyntaxTree& cst);
  
 private:
  void CheckAssignment(const Symbol* lhs, const verible::SyntaxTreeNode& rhs);
  void CheckBinaryOp(const verible::SyntaxTreeNode& op);
  void CheckFunctionCall(const verible::SyntaxTreeNode& call);
  
  TypeRegistry* types_;
  SymbolTable* symbols_;
  std::vector<TypeError> errors_;
};
```

**Tests:** `verible/verilog/analysis/type-checker_test.cc`
- Test assignment type mismatches
- Test operator type mismatches
- Test function argument mismatches
- Test width mismatches

#### 4.2 Statement Type Checking (Days 3-4)
- if/case condition types
- for loop types
- always block sensitivity

**Tests:** Statement-specific type checks

#### 4.3 Integration (Day 5)
Full type checking on real modules

---

## 🗓️ Week 5: Unused Detection

### Goal
Find unused variables, signals, functions, modules

### Tasks

#### 5.1 Usage Tracking (Days 1-2)
**File:** `verible/verilog/analysis/usage-tracker.h`

```cpp
class UsageTracker : public verible::TreeVisitorRecursive {
 public:
  struct UnusedSymbol {
    Symbol* symbol;
    Location declaration;
    std::string suggestion;  // e.g., "remove" or "prefix with _"
  };
  
  std::vector<UnusedSymbol> FindUnused();
  
 private:
  void MarkUsed(Symbol* symbol);
  bool IsUsed(const Symbol* symbol) const;
  
  SymbolTable* symbols_;
  std::set<Symbol*> used_symbols_;
};
```

**Tests:** `verible/verilog/analysis/usage-tracker_test.cc`
- Test unused variable detection
- Test unused function detection
- Test unused port detection
- Test false positives (external references)

#### 5.2 Special Cases (Days 3-4)
- Output ports always "used"
- Testbench special handling
- Generate blocks
- Assertions/covergroups

**Tests:** Edge case handling

#### 5.3 Suggestion Generation (Day 5)
Provide actionable feedback:
- "Remove unused variable 'x'"
- "Port 'y' is never driven"
- "Function 'f' is never called"

---

## 🗓️ Week 6: Call Graph & Integration

### Goal
Complete semantic analysis with call graph and full integration

### Tasks

#### 6.1 Call Graph Builder (Days 1-2)
**File:** `verible/verilog/analysis/call-graph.h`

```cpp
class CallGraph {
 public:
  struct Node {
    Symbol* function_or_task;
    std::vector<Node*> callees;
    std::vector<Node*> callers;
  };
  
  void Build(const SymbolTable& symbols);
  std::vector<Node*> GetRoots();  // Entry points
  std::vector<std::vector<Node*>> FindCycles();  // Recursive calls
  int GetCallDepth(const Symbol* func) const;
};
```

**Tests:** `verible/verilog/analysis/call-graph_test.cc`
- Test call graph construction
- Test cycle detection
- Test max depth
- Test unreachable function detection

#### 6.2 Full Integration (Days 3-4)
**File:** `verible/verilog/analysis/semantic-analyzer.h`

```cpp
class SemanticAnalyzer {
 public:
  struct AnalysisResult {
    SymbolTable symbols;
    TypeRegistry types;
    std::vector<TypeError> type_errors;
    std::vector<UnusedSymbol> unused_symbols;
    std::vector<UnresolvedReference> unresolved_refs;
    CallGraph call_graph;
  };
  
  AnalysisResult Analyze(const verible::ConcreteSyntaxTree& cst);
};
```

**Tests:** Full end-to-end tests on real SystemVerilog

#### 6.3 Performance & Polish (Day 5)
- Optimize for large files (100K+ lines)
- Add caching
- Incremental analysis support
- Final documentation

---

## 📊 Success Metrics

### Quantitative
- [ ] Symbol table: 100% symbol collection
- [ ] Type system: All SystemVerilog types represented
- [ ] Type checking: <1% false positives
- [ ] Unused detection: <5% false positives
- [ ] Performance: <1s for 10K line file

### Qualitative
- [ ] Clean, extensible architecture
- [ ] Comprehensive test coverage (>90%)
- [ ] Well-documented APIs
- [ ] Ready for IDE integration

---

## 🔧 Implementation Strategy

### Week-by-Week Approach
1. **Week 1:** Foundation (symbol table)
2. **Week 2:** Type system
3. **Week 3:** Reference resolution
4. **Week 4:** Type checking
5. **Week 5:** Unused detection
6. **Week 6:** Call graph + integration

### Testing Strategy
- Unit tests for each component
- Integration tests at week boundaries
- Real-world file tests throughout
- Performance benchmarks

### Code Organization
```
verible/
  common/analysis/     # Generic analysis infrastructure
    symbol-table.h/.cc
    scope.h/.cc
  verilog/analysis/    # Verilog-specific analysis
    symbol-table-builder.h/.cc
    type-system.h/.cc
    type-inference.h/.cc
    reference-resolver.h/.cc
    type-checker.h/.cc
    usage-tracker.h/.cc
    call-graph.h/.cc
    semantic-analyzer.h/.cc
```

---

## 🚀 Deliverables

### Code
- ~15 new source files
- ~15 new test files
- BUILD file updates
- Documentation

### Documentation
- API documentation
- Architecture overview
- Usage examples
- Performance guidelines

### Tests
- 100+ unit tests
- 20+ integration tests
- 10+ real-world file tests

---

## 💡 Future Extensions

After Phase 2 completion, this enables:
1. **Phase 3:** Enhanced IDE features (go-to-def, find-refs, rename)
2. **Refactoring tools:** Extract module, inline function
3. **Advanced linting:** Design rule checking
4. **Code generation:** Template instantiation
5. **Documentation generation:** From semantic info

---

## ✅ Ready to Start?

**Week 1 begins with Symbol Table Foundation.**

Shall I start implementing the symbol table infrastructure?

