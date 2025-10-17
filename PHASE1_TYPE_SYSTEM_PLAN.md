# Phase 1: Type System Enhancement - Detailed Plan

**Timeline**: 5 weeks (Weeks 1-5)  
**Approach**: Test-Driven Development (TDD)  
**Goal**: Comprehensive type inference and type checking

---

## 🎯 Week-by-Week Breakdown

### **Week 1: Enhanced Type Inference (Days 1-5)**

#### Day 1: Test Infrastructure Setup
- [x] Survey existing type-inference_test.cc
- [x] Survey existing type-representation.h
- [ ] Create comprehensive test fixtures
- [ ] Set up test data generators
- [ ] Document test strategy

#### Day 2-3: Expression Type Inference Tests (25 tests)
**Test Categories**:
1. Literals (5 tests)
   - Integer literals: `8'hFF`, `32'd100`, `4'b1010`
   - Real literals: `3.14`, `1.0e-6`
   - String literals: `"hello"`
   
2. Identifiers (5 tests)
   - Simple variables: `logic [7:0] a;`
   - Parameterized types: `logic [W-1:0] data;`
   - Typedef resolution: `my_type_t var;`
   
3. Concatenation & Replication (5 tests)
   - Simple concat: `{a, b, c}`
   - Nested concat: `{{a, b}, c}`
   - Replication: `{4{a}}`
   - Mixed: `{2{a}, b, 3{c}}`
   
4. Select Operations (5 tests)
   - Bit select: `a[3]`
   - Part select: `a[7:0]`
   - Indexed part select: `a[i +: 8]`
   - Multi-dimensional: `a[3:0][7:4]`
   
5. Conditional (5 tests)
   - Simple ternary: `sel ? a : b`
   - Nested ternary: `s1 ? (s2 ? a : b) : c`
   - Different widths: `sel ? 8'h00 : 16'hFFFF`

#### Day 4-5: Operator Type Inference Tests (25 tests)
**Test Categories**:
1. Binary Arithmetic (8 tests)
   - Addition: `a + b` (width propagation)
   - Subtraction: `a - b`
   - Multiplication: `a * b`
   - Division: `a / b`
   - Modulo: `a % b`
   - Signed vs unsigned operations
   
2. Binary Bitwise (6 tests)
   - AND: `a & b`
   - OR: `a | b`
   - XOR: `a ^ b`
   - Width matching rules
   
3. Binary Logical (3 tests)
   - Logical AND: `a && b`
   - Logical OR: `a || b`
   - Result type (1-bit)
   
4. Unary Operations (5 tests)
   - Negation: `-a`
   - Logical NOT: `!a`
   - Bitwise NOT: `~a`
   - Reduction: `&a`, `|a`, `^a`
   
5. Comparison (3 tests)
   - Equality: `a == b`, `a != b`
   - Relational: `a < b`, `a <= b`
   - Result type (1-bit)

**Deliverable**: 50 comprehensive type inference tests ✅

---

### **Week 2: Type Inference Implementation (Days 6-10)**

#### Day 6-7: Expression Type Inference
**Implement in `type-inference.cc`**:
- [ ] `InferConcat()` - concatenation type inference
- [ ] `InferReplication()` - replication type inference  
- [ ] `InferSelect()` - bit/part select type inference
- [ ] `InferConditional()` - ternary operator type inference

**TDD Approach**:
1. Run tests → All fail ❌
2. Implement each function
3. Run tests → Should pass ✅
4. Refactor for clarity
5. Document behavior

#### Day 8-9: Operator Type Inference
**Implement in `type-inference.cc`**:
- [ ] `InferBinaryOp()` - Enhanced for all binary operators
- [ ] `InferUnaryOp()` - Enhanced for all unary operators
- [ ] Width propagation rules
- [ ] Sign propagation rules

**Width Rules** (IEEE 1800-2017):
```cpp
// Addition: result width = max(lhs, rhs) + 1
// Example: 8-bit + 8-bit = 9-bit result

// Bitwise: result width = max(lhs, rhs)
// Example: 8-bit & 16-bit = 16-bit result

// Logical: result width = 1
// Example: (a && b) is always 1-bit
```

#### Day 10: Integration & Edge Cases
- [ ] Handle edge cases (unknown types, errors)
- [ ] Add caching for performance
- [ ] Run all 50 tests → Should pass ✅
- [ ] Measure coverage (target: 90%+)

**Checkpoint**: All 50 type inference tests passing ✅

---

### **Week 3: Type Compatibility Rules (Days 11-15)**

#### Day 11: Compatibility Test Framework (25 tests)
**Test Categories**:
1. Width Compatibility (8 tests)
   - Exact match: `logic [7:0] = logic [7:0]` ✅
   - Narrowing: `logic [7:0] = logic [15:0]` ⚠️ Warning
   - Widening: `logic [15:0] = logic [7:0]` ✅ OK
   - Width mismatch: `logic [7:0] = logic [3:0]` ⚠️

2. Sign Compatibility (8 tests)
   - Signed to signed: ✅
   - Unsigned to unsigned: ✅
   - Signed to unsigned: ⚠️ Warning
   - Unsigned to signed: ⚠️ Warning
   - Mixed arithmetic operations

3. State Compatibility (5 tests)
   - 2-state to 2-state: ✅
   - 4-state to 4-state: ✅
   - 2-state to 4-state: ✅ (safe upcast)
   - 4-state to 2-state: ⚠️ Warning (may lose X/Z)

4. Type Category Compatibility (4 tests)
   - Integral to integral: ✅
   - Real to real: ✅
   - Integral to real: ✅
   - Real to integral: ⚠️ Warning (precision loss)

#### Day 12-13: Compatibility Implementation
**Create new file: `type-compatibility-rules.{h,cc}`**

```cpp
// type-compatibility-rules.h
#ifndef VERIBLE_VERILOG_ANALYSIS_TYPE_COMPATIBILITY_RULES_H_
#define VERIBLE_VERILOG_ANALYSIS_TYPE_COMPATIBILITY_RULES_H_

#include "verible/verilog/analysis/type-representation.h"
#include "absl/status/status.h"

namespace verilog {
namespace analysis {

// Result of compatibility check
enum class CompatibilityLevel {
  kExact,           // Types match exactly
  kSafe,            // Safe implicit conversion
  kWarning,         // Conversion with potential issues (truncation, sign)
  kError,           // Incompatible types
};

struct CompatibilityResult {
  CompatibilityLevel level;
  std::string message;
  
  bool IsOk() const { 
    return level == CompatibilityLevel::kExact || 
           level == CompatibilityLevel::kSafe; 
  }
  bool IsWarning() const { return level == CompatibilityLevel::kWarning; }
  bool IsError() const { return level == CompatibilityLevel::kError; }
};

// Type compatibility checker
class TypeCompatibilityChecker {
 public:
  // Check if lhs can accept value of rhs type
  static CompatibilityResult CheckAssignment(const Type& lhs, const Type& rhs);
  
  // Check compatibility for binary operations
  static CompatibilityResult CheckBinaryOp(
      const Type& lhs, const Type& rhs, BinaryOpType op);
  
  // Check width compatibility
  static CompatibilityResult CheckWidthCompatibility(int lhs_width, int rhs_width);
  
  // Check sign compatibility
  static CompatibilityResult CheckSignCompatibility(bool lhs_signed, bool rhs_signed);
  
  // Check state compatibility (2-state vs 4-state)
  static CompatibilityResult CheckStateCompatibility(const Type& lhs, const Type& rhs);
};

}  // namespace analysis
}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_TYPE_COMPATIBILITY_RULES_H_
```

#### Day 14-15: Compatibility Implementation & Testing
- [ ] Implement all CheckCompatibility methods
- [ ] Run all 25 compatibility tests → Should pass ✅
- [ ] Add edge cases
- [ ] Document compatibility rules

**Checkpoint**: All 25 compatibility tests passing ✅

---

### **Week 4: Type Checking System (Days 16-20)**

#### Day 16: Type Checking Test Framework (30 tests)
**Test Categories**:
1. Assignment Checking (10 tests)
   - Simple assignment: `a = b;`
   - Assignment with conversion: `int_var = real_var;`
   - Assignment with width mismatch: `a[7:0] = b[15:0];`
   - Blocking vs non-blocking
   
2. Expression Checking (10 tests)
   - Binary operation type matching
   - Unary operation type validation
   - Conditional expression type matching
   - Function call argument type checking
   
3. Port Connection Checking (10 tests)
   - Module port connections
   - Interface connections
   - Width matching
   - Direction matching

#### Day 17-18: Type Checker Enhancement
**Enhance `type-checker.{h,cc}`**:

```cpp
// type-checker.h (enhanced)
class TypeChecker {
 public:
  explicit TypeChecker(const SymbolTable* symbol_table, 
                       const TypeInference* type_inference);
  
  // Check assignment type compatibility
  absl::Status CheckAssignment(const verible::Symbol& lhs, 
                               const verible::Symbol& rhs);
  
  // Check binary operation type compatibility
  absl::StatusOr<Type> CheckBinaryOperation(
      const verible::Symbol& lhs, 
      const verible::Symbol& rhs, 
      const verible::TokenInfo& op);
  
  // Check function call argument types
  absl::Status CheckFunctionCall(
      const SymbolTableNode& function,
      const std::vector<const verible::Symbol*>& args);
  
  // Check port connection types
  absl::Status CheckPortConnection(
      const PortInfo& port,
      const verible::Symbol& connection);
  
  // Get all diagnostic messages
  const std::vector<Diagnostic>& GetDiagnostics() const;
  
 private:
  const SymbolTable* symbol_table_;
  const TypeInference* type_inference_;
  TypeCompatibilityChecker compat_checker_;
  std::vector<Diagnostic> diagnostics_;
};
```

#### Day 19-20: Implementation & Integration
- [ ] Implement CheckAssignment
- [ ] Implement CheckBinaryOperation
- [ ] Implement CheckFunctionCall
- [ ] Implement CheckPortConnection
- [ ] Run all 30 type checking tests → Should pass ✅

**Checkpoint**: All 30 type checking tests passing ✅

---

### **Week 5: Integration, Testing & Documentation (Days 21-25)**

#### Day 21-22: Integration Tests (20 tests)
**Test Complete Workflows**:
1. Parse file → Build symbol table → Infer types → Check types
2. Multi-module type checking
3. Error reporting and diagnostics
4. Performance testing (large files)

**Create**: `type-system-integration_test.cc`
- [ ] 10 end-to-end tests
- [ ] 5 error cases
- [ ] 5 performance tests

#### Day 23: Documentation
**Create comprehensive documentation**:
- [ ] `TYPE_INFERENCE_GUIDE.md` - How type inference works
- [ ] `TYPE_CHECKING_GUIDE.md` - Type checking rules and examples
- [ ] API documentation (in headers)
- [ ] User guide with examples

#### Day 24: Code Review & Refactoring
- [ ] Code review checklist
- [ ] Refactor for clarity
- [ ] Optimize hot paths
- [ ] Profile and measure performance

#### Day 25: Final Testing & Validation
- [ ] Run full test suite (150+ tests)
- [ ] Check coverage (target: 85%+)
- [ ] Stress testing
- [ ] Create Phase 1 completion report

---

## 📊 Test Coverage Summary

| Category | Tests | Status |
|----------|-------|--------|
| **Week 1: Type Inference Tests** | 50 | Week 1 complete |
| **Week 3: Compatibility Tests** | 25 | Week 3 complete |
| **Week 4: Type Checking Tests** | 30 | Week 4 complete |
| **Week 5: Integration Tests** | 20 | Week 5 complete |
| **Extra Edge Cases** | 25+ | Throughout |
| **TOTAL** | **150+** | ✅ |

---

## 🎯 Success Criteria

### Must Have (End of Week 5)
- ✅ All 150+ tests passing
- ✅ Type inference for all common expressions
- ✅ Comprehensive compatibility rules
- ✅ Basic type checking (assignments, operations)
- ✅ Documentation complete
- ✅ 85%+ code coverage

### Should Have
- ✅ Port connection type checking
- ✅ Function argument type checking
- ✅ Error diagnostics with clear messages
- ✅ Performance benchmarks

### Nice to Have
- ✅ Suggested fixes for type errors
- ✅ Type inference for complex nested expressions
- ✅ Optimization (caching, lazy evaluation)

---

## 🛠️ Development Environment

### Build & Test
```bash
# Build all tests
bazel build //verible/verilog/analysis:type-inference_test
bazel build //verible/verilog/analysis:type-checker_test
bazel build //verible/verilog/analysis:type-compatibility-rules_test

# Run tests
bazel test //verible/verilog/analysis:type-inference_test
bazel test //verible/verilog/analysis:type-checker_test
bazel test //verible/verilog/analysis:all

# Run specific test
bazel test //verible/verilog/analysis:type-inference_test --test_filter=*Concatenation*

# Check coverage
bazel coverage //verible/verilog/analysis:all
```

### Code Style
- Follow existing Verible style
- Use `clang-format` for formatting
- Add comprehensive comments
- Document all public APIs

---

## 📝 Daily Progress Tracking

### Week 1 Progress
- [ ] Day 1: Test infrastructure ✅
- [ ] Day 2-3: Expression tests (50 tests) ✅
- [ ] Day 4-5: Implementation ✅

### Week 2 Progress
- [ ] Day 6-10: Type inference implementation ✅

### Week 3 Progress
- [ ] Day 11-15: Compatibility rules ✅

### Week 4 Progress
- [ ] Day 16-20: Type checking system ✅

### Week 5 Progress
- [ ] Day 21-25: Integration & docs ✅

---

## 🚀 Getting Started (Day 1)

### First Steps
1. ✅ Read existing test files
2. ✅ Understand Type representation
3. [ ] Create test plan document
4. [ ] Set up test fixtures
5. [ ] Write first 10 tests
6. [ ] Run tests (should fail)
7. [ ] Begin implementation

**Let's start with Day 1, Task 1: Create comprehensive test fixtures!**

---

**Status**: Ready to begin Day 1! 🎉  
**Next**: Create test fixtures and first batch of tests

