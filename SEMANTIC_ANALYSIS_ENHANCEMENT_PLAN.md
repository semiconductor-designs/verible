# Verible Semantic Analysis Enhancement Plan

**Date**: October 17, 2025  
**Version**: v5.0.1  
**Status**: Comprehensive enhancement roadmap for semantic analysis

---

## 🎯 Executive Summary

Verible has achieved **100% parsing completeness** for IEEE 1800-2017 SystemVerilog. The next frontier is **enhanced semantic analysis** to enable:
- Advanced type checking and validation
- Better error diagnostics
- Cross-module analysis
- Call graph construction
- Data flow analysis
- Unused code detection (enhanced)

### Current State Assessment

| Feature | Status | Quality | Gap |
|---------|--------|---------|-----|
| **Parsing** | ✅ 100% | ⭐⭐⭐⭐⭐ | None |
| **Symbol Table** | ✅ Complete | ⭐⭐⭐⭐⭐ | None |
| **Type Inference** | ⚠️ Partial | ⭐⭐⭐ | Expression types |
| **Type Checking** | ⚠️ Basic | ⭐⭐ | Comprehensive validation |
| **Unused Detection** | ⚠️ Basic | ⭐⭐⭐ | Cross-module, data flow |
| **Call Graph** | ✅ Basic | ⭐⭐⭐ | Enhanced analysis |
| **Cross-Module** | ⚠️ Partial | ⭐⭐ | Full validation |
| **Data Flow** | ❌ Missing | - | Needed |

---

## 📊 What Already Exists

### 1. Symbol Table ✅ EXCELLENT

**Location**: `verible/verilog/analysis/symbol-table.{h,cc}`  
**Size**: 2937 lines (550 header + 2387 implementation)  
**Quality**: Production-grade, battle-tested

**Capabilities**:
- ✅ Symbol collection from CST
- ✅ Hierarchical scoping
- ✅ Reference resolution (unqualified, direct member, member of type)
- ✅ Import/inheritance handling
- ✅ Multi-file support via VerilogProject
- ✅ Complete SystemVerilog construct coverage

**Example**:
```cpp
SymbolTable symbol_table(&project);
symbol_table.Build(diagnostics);
symbol_table.Resolve(diagnostics);

// Now all symbols are discovered and references are resolved!
const auto& root = symbol_table.Root();
```

**Verdict**: **DO NOT MODIFY** - This is excellent infrastructure! ✅

---

### 2. Type Inference ⚠️ PARTIAL

**Location**: `verible/verilog/analysis/type-inference.{h,cc}`  
**Status**: Framework exists, partial implementation  
**Lines**: ~430 total

**What Exists**:
- ✅ TypeInference class with caching
- ✅ GetDeclaredType() - gets type from symbol table
- ✅ InferType() - infers expression types
- ✅ InferBinaryOp() - binary operation type inference
- ✅ InferUnaryOp() - unary operation type inference
- ✅ Cache system for performance

**What's Partial/Missing**:
- ⚠️ Limited expression type inference (basic cases only)
- ⚠️ No struct/union member type resolution
- ⚠️ No parameterized type handling
- ⚠️ No function return type inference
- ⚠️ No implicit cast rules

**Example (Current)**:
```cpp
TypeInference inference(&symbol_table);
const Type* expr_type = inference.InferType(*expression_node);
// Works for simple cases, returns nullptr for complex expressions
```

**Enhancement Needed**: ⭐⭐⭐⭐ HIGH PRIORITY

---

### 3. Type Checking ⚠️ BASIC

**Location**: `verible/verilog/analysis/type-checker.{h,cc}`  
**Status**: Basic framework exists  
**Lines**: ~200 total

**What Exists**:
- ✅ TypeChecker class
- ✅ Basic type compatibility checks
- ✅ Simple assignment validation

**What's Missing**:
- ❌ Comprehensive compatibility rules (signed/unsigned, width, 2-state/4-state)
- ❌ Implicit conversion validation
- ❌ Function argument type checking
- ❌ Port connection type checking
- ❌ Expression context validation (e.g., casez requires 4-state)

**Enhancement Needed**: ⭐⭐⭐⭐⭐ CRITICAL PRIORITY

---

### 4. Unused Detection ⚠️ BASIC

**Location**: `verible/verilog/analysis/unused-detector.{h,cc}`  
**Status**: Basic implementation exists  
**Lines**: ~116 total

**What Exists**:
- ✅ UnusedDetector class
- ✅ Finds symbols declared but not referenced
- ✅ Configuration options (ignore parameters, private members, etc.)
- ✅ Reports unused variables, functions, parameters

**What's Missing**:
- ❌ Cross-module unused detection
- ❌ Data flow analysis (assigned but never read)
- ❌ Dead code detection (unreachable code)
- ❌ Unused port detection
- ❌ Unused import detection

**Example (Current)**:
```cpp
UnusedDetector detector(&symbol_table);
detector.Analyze();
for (const auto& unused : detector.GetUnusedSymbols()) {
  std::cout << "Unused: " << unused.name << " in " << unused.scope << "\n";
}
```

**Enhancement Needed**: ⭐⭐⭐⭐ HIGH PRIORITY

---

### 5. Call Graph ✅ BASIC

**Location**: `verible/verilog/analysis/call-graph.{h,cc}`  
**Status**: Basic implementation exists

**What Exists**:
- ✅ Call graph construction
- ✅ Function/task call tracking

**What's Missing**:
- ❌ Cross-module call tracking
- ❌ Indirect calls (function pointers, dynamic calls)
- ❌ Cycle detection
- ❌ Unused function detection via call graph

**Enhancement Needed**: ⭐⭐⭐ MEDIUM PRIORITY

---

### 6. Linter Rules ✅ EXTENSIVE

**Location**: `verible/verilog/analysis/checkers/`  
**Count**: 60+ semantic checker rules  
**Status**: Production-quality

**Examples**:
- `always-comb-blocking-rule` - checks assignment types in always_comb
- `explicit-parameter-storage-type-rule` - checks parameter type declarations
- `case-missing-default-rule` - semantic correctness checks
- `dff-name-style-rule` - behavioral pattern recognition

**Verdict**: **EXCELLENT** - These are semantic analyzers working in production! ✅

---

## 🎯 Enhancement Priorities

### Priority 1: Type Checking System ⭐⭐⭐⭐⭐ CRITICAL

**Goal**: Comprehensive type validation for all SystemVerilog expressions

**What to Build**:

1. **Type Compatibility Rules**
   - Signed/unsigned compatibility
   - Width compatibility (explicit and implicit)
   - 2-state/4-state compatibility
   - Real/integer compatibility
   - Struct/union compatibility
   - Enum compatibility
   - Class type compatibility (inheritance)

2. **Expression Type Validation**
   - Binary operation type checking (`a + b`, `a & b`, etc.)
   - Unary operation type checking (`!a`, `~a`, `+a`)
   - Ternary operation type checking (`sel ? a : b`)
   - Function call argument type checking
   - Assignment type checking (`a = b`)
   - Port connection type checking

3. **Context-Aware Validation**
   - `casez`/`casex` require 4-state logic
   - `unique`/`priority` require specific types
   - Bit-select requires integral types
   - Part-select requires packed types

**Example Enhancements**:
```cpp
// Enhanced TypeChecker
class TypeChecker {
 public:
  // Check assignment compatibility
  absl::Status CheckAssignment(const Type& lhs, const Type& rhs);
  
  // Check binary operation types
  absl::StatusOr<Type> CheckBinaryOp(const Type& lhs, const Type& rhs, OpType op);
  
  // Check function call argument types
  absl::Status CheckFunctionCall(const Function& func, const std::vector<Type>& args);
  
  // Check port connection types
  absl::Status CheckPortConnection(const Port& port, const Type& connection);
};
```

**Effort**: 4-5 weeks  
**Value**: ⭐⭐⭐⭐⭐ (enables comprehensive error detection)

---

### Priority 2: Enhanced Type Inference ⭐⭐⭐⭐ HIGH

**Goal**: Infer types for all SystemVerilog expressions

**What to Enhance**:

1. **Expression Type Inference**
   - Concatenation (`{a, b, c}`)
   - Replication (`{N{a}}`)
   - Bit-select (`a[3]`)
   - Part-select (`a[7:0]`)
   - Function calls (`func(args)`)
   - Ternary (`sel ? a : b`)
   - Struct/union member access (`s.field`)
   - Array indexing (`arr[i]`)

2. **Type Propagation**
   - Through assignments
   - Through function calls
   - Through port connections

3. **Parameterized Type Resolution**
   - Class parameters (`class C #(type T);`)
   - Module parameters (`module M #(parameter int W);`)

4. **Function Return Type Inference**
   - From function declaration
   - From return statements

**Example**:
```systemverilog
logic [7:0] a, b;
logic [15:0] result;

// Should infer: {a, b} has type logic [15:0]
result = {a, b};  // OK: types match

// Should infer: a + b has type logic [8:0] (one bit wider)
result = a + b;  // Warning: truncation
```

**Effort**: 3-4 weeks  
**Value**: ⭐⭐⭐⭐⭐ (foundation for type checking)

---

### Priority 3: Cross-Module Analysis ⭐⭐⭐⭐ HIGH

**Goal**: Validate references and types across module boundaries

**What to Build**:

1. **Cross-Module Reference Validation**
   - Hierarchical references (`top.sub.signal`)
   - Interface connections
   - Modport validation
   - Bind statement validation

2. **Port Connection Validation**
   - Width matching
   - Direction matching (input/output/inout)
   - Type compatibility

3. **Parameter Propagation**
   - Track parameter values across hierarchy
   - Validate parameter overrides
   - Check parameter-dependent types

**Example**:
```systemverilog
module top;
  logic [7:0] data;
  sub u_sub(.data_in(data));  // Check: data_in width matches data
endmodule

module sub(input logic [7:0] data_in);
  // ...
endmodule
```

**Effort**: 3-4 weeks  
**Value**: ⭐⭐⭐⭐ (catches integration errors early)

---

### Priority 4: Enhanced Unused Detection ⭐⭐⭐ MEDIUM

**Goal**: Comprehensive unused code detection with data flow

**What to Enhance**:

1. **Data Flow Analysis**
   - Variables assigned but never read
   - Variables read before assignment (uninitialized)
   - Write-only signals
   - Read-only signals (constants)

2. **Cross-Module Unused Detection**
   - Modules instantiated but not used
   - Functions defined but never called (even cross-file)
   - Parameters defined but never used

3. **Dead Code Detection**
   - Unreachable code (after return, break, etc.)
   - Conditions that are always true/false
   - Redundant assignments

**Example**:
```systemverilog
module test;
  logic [7:0] a, b, c;
  
  always_comb begin
    a = 8'h00;       // WARNING: 'a' assigned but never read
    b = a + 1;
    c = b;
    // 'c' is assigned but never read
  end
endmodule
```

**Effort**: 2-3 weeks  
**Value**: ⭐⭐⭐⭐ (code quality, optimization opportunities)

---

### Priority 5: Enhanced Call Graph ⭐⭐⭐ MEDIUM

**Goal**: Comprehensive function/task dependency analysis

**What to Enhance**:

1. **Cross-Module Call Tracking**
   - Track calls across files
   - Track calls across packages
   - Track DPI-C calls

2. **Advanced Analysis**
   - Cycle detection (recursive calls)
   - Unused function detection via reachability
   - Call depth analysis

3. **Visualization**
   - Export to DOT format
   - Call hierarchy view

**Example**:
```cpp
CallGraph graph(&symbol_table);
graph.Build();

// Find all callers of a function
auto callers = graph.GetCallers("my_function");

// Find all callees
auto callees = graph.GetCallees("my_function");

// Detect cycles
auto cycles = graph.DetectCycles();

// Export to DOT
graph.ExportToDOT("call_graph.dot");
```

**Effort**: 2-3 weeks  
**Value**: ⭐⭐⭐ (code navigation, refactoring support)

---

### Priority 6: Data Flow Analysis ⭐⭐⭐ MEDIUM

**Goal**: Track data dependencies through code

**What to Build**:

1. **Def-Use Chains**
   - Track where variables are defined
   - Track where variables are used
   - Identify dependencies

2. **Reaching Definitions**
   - Which definitions reach each use
   - Detect uninitialized reads

3. **Live Variable Analysis**
   - Which variables are live at each point
   - Optimize register allocation

**Effort**: 3-4 weeks  
**Value**: ⭐⭐⭐ (optimization, error detection)

---

## 🗓️ Implementation Roadmap

### Phase 1: Type System (Weeks 1-5)

**Week 1-2: Enhanced Type Inference**
- Implement expression type inference
- Add struct/union member resolution
- Add parameterized type resolution
- 50+ tests for coverage

**Week 3-4: Type Checking Core**
- Implement compatibility rules
- Add expression validation
- Add assignment checking
- 100+ tests

**Week 5: Type Checking Integration**
- Function argument checking
- Port connection checking
- Context-aware validation
- Integration tests

**Deliverables**:
- `type-inference.{h,cc}` - Enhanced (600+ lines)
- `type-checker.{h,cc}` - Enhanced (800+ lines)
- `type-compatibility-rules.{h,cc}` - New (400+ lines)
- 150+ tests
- Documentation

---

### Phase 2: Cross-Module Analysis (Weeks 6-9)

**Week 6: Cross-Module Infrastructure**
- Multi-file symbol resolution
- Hierarchical reference tracking
- 30+ tests

**Week 7-8: Port & Connection Validation**
- Port connection type checking
- Interface connection validation
- Modport checking
- 50+ tests

**Week 9: Parameter Propagation**
- Parameter value tracking
- Parameter override validation
- 30+ tests

**Deliverables**:
- `cross-module-analyzer.{h,cc}` - New (600+ lines)
- `port-connection-validator.{h,cc}` - New (400+ lines)
- 110+ tests
- Documentation

---

### Phase 3: Enhanced Unused & Flow (Weeks 10-12)

**Week 10: Data Flow Analysis**
- Def-use chain construction
- Reaching definitions
- 40+ tests

**Week 11: Enhanced Unused Detection**
- Cross-module unused detection
- Data flow-based unused detection
- 40+ tests

**Week 12: Call Graph Enhancement**
- Cross-module call tracking
- Cycle detection
- 30+ tests

**Deliverables**:
- `data-flow-analyzer.{h,cc}` - New (500+ lines)
- `unused-detector.{h,cc}` - Enhanced (300+ lines)
- `call-graph.{h,cc}` - Enhanced (200+ lines)
- 110+ tests
- Documentation

---

## 📈 Expected Outcomes

### Quantitative Improvements

| Metric | Before | After | Improvement |
|--------|--------|-------|-------------|
| **Type Errors Detected** | Basic | Comprehensive | 5-10x |
| **Unused Code Detection** | Simple | Data-flow based | 3-5x |
| **Cross-Module Validation** | Limited | Full | New |
| **False Positives** | Some | Minimal | -80% |
| **Analysis Completeness** | 60% | 95% | +35% |

### Qualitative Improvements

1. **Better Error Messages**
   - "Type mismatch: expected logic [7:0], got logic [15:0]"
   - "Port 'data_in' expects 8 bits, connected to 16-bit signal"
   - "Variable 'x' assigned but never read"

2. **Catch More Errors**
   - Width mismatches
   - Sign mismatches
   - Uninitialized reads
   - Dead code
   - Type incompatibilities

3. **Enable Advanced Features**
   - Safe refactoring
   - Automated fixes
   - Code optimization suggestions
   - Better IDE integration

---

## 🛠️ Development Approach

### Test-Driven Development (TDD)

**For Each Feature**:
1. Write test cases first
2. Implement feature to pass tests
3. Refactor for clarity
4. Add edge case tests
5. Document behavior

**Example**:
```cpp
// Test: Type checking for binary addition
TEST(TypeChecker, BinaryAddition) {
  // logic [7:0] + logic [7:0] -> logic [8:0]
  Type lhs = IntegralType(8, false, false);  // 8-bit unsigned
  Type rhs = IntegralType(8, false, false);
  auto result = type_checker.CheckBinaryOp(lhs, rhs, OpType::kAdd);
  ASSERT_TRUE(result.ok());
  EXPECT_EQ(result.value().width, 9);  // Result is one bit wider
}
```

---

### Integration with Existing Code

**Principles**:
1. ✅ Build on existing symbol table (don't modify)
2. ✅ Extend existing TypeInference/TypeChecker
3. ✅ Follow existing code patterns
4. ✅ Maintain backward compatibility
5. ✅ Use existing test infrastructure

---

### Code Quality Standards

1. **Documentation**
   - Every public API documented
   - Examples for complex features
   - Design rationale documented

2. **Testing**
   - 80%+ code coverage
   - Edge cases covered
   - Negative tests (error cases)

3. **Performance**
   - Caching for expensive operations
   - Incremental analysis where possible
   - Profiling and optimization

4. **Maintainability**
   - Clear naming conventions
   - Modular design
   - Minimal coupling

---

## 🎯 Success Criteria

### Must-Have (v5.1.0)
- ✅ Comprehensive type checking for expressions
- ✅ Type compatibility rules (signed/unsigned, width)
- ✅ Enhanced type inference (all common expressions)
- ✅ Cross-module port connection validation
- ✅ 300+ new tests, all passing

### Should-Have (v5.2.0)
- ✅ Data flow analysis (def-use chains)
- ✅ Enhanced unused detection (cross-module, data flow)
- ✅ Enhanced call graph (cycles, reachability)
- ✅ 100+ additional tests

### Nice-to-Have (v5.3.0)
- ✅ Advanced data flow (live variable analysis)
- ✅ Automated fix suggestions
- ✅ Performance optimization (caching, incremental)
- ✅ Visualization tools (call graph, data flow)

---

## 📊 Risk Assessment

### Technical Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Complex type system | Medium | High | Incremental implementation, extensive tests |
| Performance degradation | Low | Medium | Profiling, caching, lazy evaluation |
| False positives | Medium | High | Conservative checks, user configuration |
| Backward compatibility | Low | High | Careful API design, versioning |

### Schedule Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Underestimate complexity | Medium | Medium | Buffer time, phased delivery |
| Scope creep | Medium | Medium | Strict prioritization, MVP first |
| Testing takes longer | High | Low | Parallel development, continuous testing |

---

## 💼 Resource Requirements

### Development Time
- **Phase 1** (Type System): 5 weeks
- **Phase 2** (Cross-Module): 4 weeks
- **Phase 3** (Unused/Flow): 3 weeks
- **Total**: 12 weeks (~3 months)

### Infrastructure
- ✅ Existing build system (Bazel)
- ✅ Existing test framework
- ✅ Existing symbol table
- ✅ Existing parsers (100% complete)

### Documentation
- API documentation (integrated)
- User guides (incremental)
- Design documents (as needed)

---

## 🚀 Next Steps

### Immediate Actions

1. **Review & Approval** (This Document)
   - Get stakeholder approval
   - Prioritize features
   - Confirm timeline

2. **Phase 1 Kickoff** (Week 1)
   - Set up development branch
   - Create issue tracking
   - Begin type inference enhancements

3. **Weekly Progress Reviews**
   - Track against roadmap
   - Adjust priorities as needed
   - Report progress

---

## ✅ Summary

**Current State**: 100% parsing, basic semantic analysis  
**Goal**: Comprehensive semantic analysis with type checking, cross-module validation, and data flow  
**Timeline**: 12 weeks (3 months)  
**Effort**: High value, manageable scope  
**Risk**: Low-medium, well-mitigated

**The semantic analysis enhancements will transform Verible from a parser into a comprehensive SystemVerilog analysis platform capable of catching errors, enabling refactoring, and providing deep code insights.**

---

**Status**: Ready to begin Phase 1 🚀  
**Question**: **Which priority should we start with?** (Recommend: Priority 1 - Type Checking System)

