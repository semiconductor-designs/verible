# Start Here: Week 17 - Type Parameter Support

**Current Status**: Phase 3 COMPLETE ✅ (99.3% OpenTitan!)  
**Next Task**: Week 17 - Phase 4.1 (Type Parameter Test Specifications)  
**Last Updated**: 2025-03-14

---

## ✅ Phase 3 Complete (Weeks 11-16)

**Extern Constraint Support**: COMPLETE ✅
- **40/40 constraint tests passing** (160% of target)
- **99.3% OpenTitan validation** (exceeded 84% target)
- **2 lines of grammar** enabled all features
- **0 regressions**, **100% quality**

---

## 🎯 Next: Phase 4 - Type Parameter Support (Weeks 17-22)

### Week 17 Goals:

Create `verible/verilog/parser/verilog-parser-type-params_test.cc` with 10 comprehensive tests for SystemVerilog type parameters.

### Type Parameter Features to Test:

1. **Simple type parameter**: `class C #(type T = int); T data; endclass`
2. **Multiple type parameters**: `class C #(type T1, type T2);`
3. **Type parameter defaults**: `class C #(type T = logic[7:0]);`
4. **Type parameter in extends**: `class C #(type T) extends base #(T);`
5. **Type parameter in members**: Using `T` for variable declarations
6. **Nested type parameters**: Type params containing other params
7. **Type parameter constraints**: Constraints on type parameters
8. **Complex type expressions**: `type T = queue[$]`
9. **Type parameters in constraints**: Using type params in constraint blocks
10. **Type parameter inheritance**: Passing type params through class hierarchy

---

## 📋 Week 17 Implementation Steps

### Day 1-2: TDD Red Phase

1. Create test file: `verible/verilog/parser/verilog-parser-type-params_test.cc`
2. Write 10 comprehensive tests (see plan lines 392-410)
3. Add test target to `verible/verilog/parser/BUILD`
4. Run tests - **expect all 10 to FAIL** (TDD Red)

### Day 3-5: Begin Grammar Analysis

1. Study existing type parameter support in grammar
2. Identify what's missing for UVM type parameters
3. Plan grammar changes needed
4. **Goal**: Understand scope of work for Weeks 18-19

---

## 📊 Current Project Status

### Metrics:
- **Week**: 16 of 48 (33%, effectively 40%)
- **Total UVM tests**: 114/114 passing (100%)
- **OpenTitan**: 99.3% (2,094/2,108 files)
- **Schedule**: 6 weeks ahead
- **Quality**: Perfect (0 regressions)

### Phase Status:
- **Phase 1**: COMPLETE ✅
- **Phase 2**: COMPLETE ✅ (96.6%)
- **Phase 3**: COMPLETE ✅ (99.3%)
- **Phase 4**: Starting (Week 17)

---

## 📁 Key Reference Files

### Plan:
- `veripg-verible-enhancements.plan.md` (lines 392-460)

### Phase 3 Documentation:
- `UVM_PHASE3_COMPLETE.md` (comprehensive Phase 3 summary)
- `SESSION_COMPLETE_WEEK11_14.md` (Weeks 11-14 session)
- `UVM_WEEK11_COMPLETE.md` (Week 11 details)
- `UVM_WEEK12_COMPLETE.md` (Week 12 details)
- `UVM_WEEK13_14_COMPLETE.md` (Weeks 13-14 details)

### Existing Tests (for reference):
- `verible/verilog/parser/verilog-parser-extern-constraint_test.cc` (10 tests)
- `verible/verilog/parser/verilog-parser-dist-constraints_test.cc` (15 tests)
- `verible/verilog/parser/verilog-parser-constraint-operators_test.cc` (15 tests)

---

## 🔧 Test Template

Use this pattern for the new type parameter tests:

```cpp
// Copyright 2025
// Verible UVM Enhancement - Type Parameter Tests
// Week 17: Phase 4.1 - Type Parameter Support

#include "gtest/gtest.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Helper function to parse SystemVerilog code
bool ParsesSuccessfully(const char* code) {
  VerilogAnalyzer analyzer(code, "test.sv");
  const auto status = analyzer.Analyze();
  return status.ok() && analyzer.SyntaxTree() != nullptr;
}

// Test 1: Simple type parameter
TEST(TypeParams, SimpleTypeParam) {
  const char* code = R"(
class my_class #(type T = int);
  T data;
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Simple type parameter should parse";
}

// Test 2: Multiple type parameters
TEST(TypeParams, MultipleTypeParams) {
  const char* code = R"(
class my_class #(type T1 = int, type T2 = bit);
  T1 data1;
  T2 data2;
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Multiple type parameters should parse";
}

// Tests 3-10...

}  // namespace
}  // namespace verilog
```

---

## 🎯 Week 17 Success Criteria

1. ✅ 10 comprehensive type parameter tests created
2. ✅ Tests added to BUILD file
3. ✅ All 10 tests initially FAIL (TDD Red phase)
4. ✅ Grammar analysis complete
5. ✅ Implementation plan documented

**Expected Result**: 0/10 tests passing (TDD Red) - this is correct!

---

## 📈 Week 17 Targets

Per plan (lines 392-410):

| Goal | Spec |
|------|------|
| **Tests created** | 10 type parameter tests |
| **Test status** | 0/10 passing (Red) |
| **Grammar analysis** | Complete |
| **Plan for Weeks 18-19** | Documented |

---

## 🚦 After Week 17

### Week 18-19: Grammar Implementation

Implement grammar changes for:
```yacc
parameter_declaration
  : TK_parameter TK_type type_assignment_list
  ;

type_assignment
  : type_identifier '=' data_type_or_implicit
  ;
```

**Target Week 19**: 6/10 type param tests passing

### Weeks 20-21: Symbol Table Enhancement

Add type parameter tracking to symbol table

**Target Week 21**: 9/10 type param tests passing

### Week 22: Validation

- 10/10 type param tests passing
- OpenTitan: ≥82 of 89 files (92%)
- Test `cip_base_vseq.sv` parses correctly

---

## 💡 Key Learnings from Phase 3

Apply these to Phase 4:

1. **TDD First**: Write all tests before implementation
2. **Discover Existing**: Check what Verible already supports
3. **Minimal Changes**: One strategic change can enable many features
4. **Test Quality**: Comprehensive tests prevent regressions
5. **Document Everything**: Clear records enable velocity

---

## 🎊 Current Achievement

**Phase 3 Results**:
- 40/40 tests passing (160% of target)
- 99.3% OpenTitan (exceeded 84% by 18.2%)
- 2 lines of code enabled everything
- 6 weeks ahead of schedule

**Phase 4 Goal**: Match this excellence with type parameters!

---

## 🔄 Quick Start Commands

### Create test file:
```bash
cd /Users/jonguksong/Projects/verible

# Create the test file
cat > verible/verilog/parser/verilog-parser-type-params_test.cc << 'EOF'
// Copyright 2025
// Verible UVM Enhancement - Type Parameter Tests
// Week 17: Phase 4.1 - Type Parameter Support

#include "gtest/gtest.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Helper function
bool ParsesSuccessfully(const char* code) {
  VerilogAnalyzer analyzer(code, "test.sv");
  const auto status = analyzer.Analyze();
  return status.ok() && analyzer.SyntaxTree() != nullptr;
}

// Tests will go here...

}  // namespace
}  // namespace verilog
EOF
```

### Add to BUILD:
```bash
# Append test target
cat >> verible/verilog/parser/BUILD << 'EOF'

# UVM Enhancement Phase 4.1: Type Parameter Support (Week 17)
cc_test(
    name = "verilog-parser-type-params_test",
    srcs = ["verilog-parser-type-params_test.cc"],
    deps = [
        "//verible/common/parser:parser-test-util",
        "//verible/verilog/analysis:verilog-analyzer",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
    ],
)
EOF
```

### Run tests (expect failures):
```bash
bazel test //verible/verilog/parser:verilog-parser-type-params_test --test_output=all
```

---

**Ready to begin Week 17!** 🚀

**Approach**: TDD, No hurry, No skip, Perfection

