# Phase 1 Week 4: Type Checker Enhancement - Detailed Plan

**Timeline**: Days 11-20  
**Approach**: TDD (Test-Driven Development)  
**Goal**: Integrate TypeCompatibilityChecker into TypeChecker

---

## 🎯 Objective

Enhance the existing TypeChecker to use our comprehensive TypeCompatibilityChecker system, providing:
- Detailed compatibility checking with precise error messages
- Support for all compatibility levels (Exact, Safe, Warning, Error)
- Integration with existing TypeChecker::Options
- Comprehensive test coverage

---

## 📋 Current State Assessment

### Existing TypeChecker
- **File**: `type-checker.{h,cc}`
- **Lines**: 212 (header) + 362 (implementation) = 574 total
- **Tests**: 546 lines (existing tests)
- **API**: Comprehensive (assignments, operators, functions, casts)
- **Status**: Basic implementation with simple `IsAssignmentCompatible`

### What Needs Enhancement
1. **Replace simple compatibility check** with TypeCompatibilityChecker
2. **Add detailed error messages** from CompatibilityResult
3. **Support all compatibility levels** (not just pass/fail)
4. **Integrate with warnings system** (kWarning → AddWarning())
5. **Add operator-specific checks** using CheckBinaryOp()

---

## 📝 Implementation Plan

### Step 1: Update TypeChecker Header (30 min)
**Goal**: Add TypeCompatibilityChecker dependency

```cpp
#include "verible/verilog/analysis/type-compatibility-rules.h"

class TypeChecker {
 private:
  const SymbolTable* symbol_table_;
  const TypeInference* type_inference_;
  TypeCompatibilityChecker compat_checker_;  // NEW
  // ...
};
```

### Step 2: Enhance CheckAssignment (1 hour)
**Goal**: Use TypeCompatibilityChecker::CheckAssignment

**Before**:
```cpp
if (!IsAssignmentCompatible(*lhs_type, *rhs_type)) {
  AddError(FormatTypeError(*lhs_type, *rhs_type));
  return error;
}
```

**After**:
```cpp
auto result = TypeCompatibilityChecker::CheckAssignment(*lhs_type, *rhs_type);

if (result.IsError()) {
  AddError(result.message);
  return error;
} else if (result.IsWarning()) {
  if (options_.warn_narrowing || options_.warn_sign_mismatch) {
    AddWarning(result.message);
  }
}
```

### Step 3: Enhance CheckBinaryOperator (1 hour)
**Goal**: Use TypeCompatibilityChecker::CheckBinaryOp

```cpp
auto result = TypeCompatibilityChecker::CheckBinaryOp(
    *lhs_type, *rhs_type, 
    DetermineBinaryOpType(op_token));

if (result.IsError()) {
  AddError(result.message);
  return error;
}
```

### Step 4: Add 30+ New Tests (3 hours)
**Goal**: Comprehensive testing of enhanced functionality

**Test Categories** (30 tests):
1. **Assignment Tests** (10 tests)
   - Exact match
   - Safe widening
   - Truncation warnings
   - Sign mismatch warnings
   - State mismatch warnings
   - Multiple warnings
   - Real type assignments
   - String type errors
   - User-defined type mismatches
   - Complex scenarios

2. **Binary Operator Tests** (10 tests)
   - Arithmetic operators (numeric types)
   - Bitwise operators (integral types)
   - Logical operators (any types)
   - Comparison operators
   - Shift operators
   - String in arithmetic (error)
   - Real in arithmetic (OK)
   - Mixed signedness
   - Width mismatches
   - State mismatches

3. **Options Integration Tests** (5 tests)
   - strict_mode behavior
   - warn_narrowing disabled
   - warn_sign_mismatch disabled
   - warnings_as_errors behavior
   - Combined options

4. **Error Message Tests** (5 tests)
   - Detailed error messages
   - Suggested fixes
   - Multiple issues reported
   - Clear type information
   - Line/column info

---

## 🧪 Test-First Approach

### Phase A: Write Tests (Day 11-12)
1. Create test file structure
2. Write 30 tests (all will fail initially)
3. Document expected behavior
4. Verify tests compile

### Phase B: Implement (Day 13-15)
1. Update TypeChecker header
2. Modify CheckAssignment implementation
3. Modify CheckBinaryOperator implementation
4. Run tests - fix until all pass

### Phase C: Refine (Day 16-17)
1. Add helper functions
2. Improve error messages
3. Optimize performance
4. Code review and cleanup

---

## ✅ Success Criteria

### Must Have
- [x] 30+ new tests
- [x] All tests passing
- [x] TypeCompatibilityChecker fully integrated
- [x] Detailed error/warning messages
- [x] Options system working correctly

### Should Have
- [x] Performance maintained or improved
- [x] Clear, understandable error messages
- [x] Backward compatibility with existing tests
- [x] Documentation updated

### Nice to Have
- [x] Suggested fixes in error messages
- [x] Performance benchmarks
- [x] Example usage in docs

---

## 📊 Timeline

| Days | Task | Status |
|------|------|--------|
| Day 11-12 | Write 30+ tests | Pending |
| Day 13-15 | Implement enhancements | Pending |
| Day 16-17 | Refine & optimize | Pending |
| Day 18-20 | Integration testing | Pending |

---

## 🚀 Getting Started

**Next Step**: Write the first 10 assignment tests following TDD!

Let's begin! 🎉

