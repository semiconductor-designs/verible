# UVM Phase 2.2: Preprocessor Integration - Next Steps

**Date**: 2025-01-18  
**Current Phase**: 2.2 - Preprocessor Integration  
**Previous Phase**: 2.1 - UVM Macro Registry ✅ COMPLETE (15/15 tests passed)  
**Status**: Ready to Begin Implementation

---

## Executive Summary

Phase 2.1 successfully created a comprehensive UVM macro registry with 29 macros and 100% test coverage. Phase 2.2 will integrate this registry into Verible's preprocessor, making UVM macros available during parsing without requiring external UVM library files.

---

## Understanding Verible's Preprocessor Architecture

### Key Data Structures

**`VerilogPreprocessData`** (from `verilog-preprocess.h:70-90`):
```cpp
struct VerilogPreprocessData {
  using MacroDefinition = verible::MacroDefinition;
  using MacroDefinitionRegistry = std::map<std::string_view, MacroDefinition>;
  
  // Map of defined macros (user-defined + built-in)
  MacroDefinitionRegistry macro_definitions;
  
  verible::TokenStreamView preprocessed_token_stream;
  std::vector<VerilogPreprocessError> errors;
  std::vector<VerilogPreprocessError> warnings;
};
```

**`VerilogPreprocess`** (from `verilog-preprocess.h:94+`):
```cpp
class VerilogPreprocess {
  struct Config {
    bool filter_branches = false;
    bool include_files = false;
    bool expand_macros = false;
  };
  
  VerilogPreprocessData ScanStream(const TokenStreamView &token_stream);
  
private:
  absl::Status HandleMacroIdentifier(...);
  absl::Status HandleDefine(...);
  absl:Status HandleUndef(...);
  // ...
};
```

###Integration Strategy

**Goal**: When a macro is referenced (e.g., `` `uvm_object_utils(MyClass)``), check if it's a UVM macro BEFORE looking in user-defined macros.

**Priority Order**:
1. User-defined macros (highest priority - user can override UVM)
2. UVM built-in macros (from our registry)
3. Undefined (error)

**Implementation Point**: `HandleMacroIdentifier()` method in `verilog-preprocess.cc`

---

## Phase 2.2 Implementation Plan

### Step 1: Add UVM Registry Dependency to Preprocessor

**File**: `verible/verilog/preprocessor/BUILD`

**Action**: Add `uvm-macros` dependency to `verilog-preprocess` library

```python
cc_library(
    name = "verilog-preprocess",
    srcs = ["verilog-preprocess.cc"],
    hdrs = ["verilog-preprocess.h"],
    deps = [
        ":uvm-macros",  # NEW: Add UVM macro registry
        ":verilog-preprocess-expr",
        # ... existing deps ...
    ],
)
```

**Status**: ⏳ TODO

---

### Step 2: Include UVM Registry Header

**File**: `verible/verilog/preprocessor/verilog-preprocess.cc`

**Action**: Add include at top of file

```cpp
#include "verible/verilog/preprocessor/verilog-preprocess.h"

// ... existing includes ...

#include "verible/verilog/preprocessor/uvm-macros.h"  // NEW

namespace verilog {
```

**Status**: ⏳ TODO

---

### Step 3: Add UVM Macro Lookup Helper Method

**File**: `verible/verilog/preprocessor/verilog-preprocess.cc`

**Action**: Add private method to VerilogPreprocess class

```cpp
// In VerilogPreprocess class (private section)

// Check if macro name is a built-in UVM macro and convert to MacroDefinition
// Returns nullptr if not a UVM macro
std::unique_ptr<verible::MacroDefinition> LookupUVMMacro(
    std::string_view macro_name) const {
  using preprocessor::UVMMacroRegistry;
  
  if (!UVMMacroRegistry::IsUVMMacro(macro_name)) {
    return nullptr;
  }
  
  const auto* uvm_def = UVMMacroRegistry::GetMacro(macro_name);
  if (!uvm_def) {
    return nullptr;
  }
  
  // Convert UVMMacroDef to verible::MacroDefinition
  auto macro_def = std::make_unique<verible::MacroDefinition>();
  macro_def->SetName(uvm_def->name);
  
  // Add parameters
  for (const auto& param : uvm_def->parameters) {
    macro_def->AppendParameter(MacroParameterInfo{param});
  }
  
  // Set body (simplified for now - Phase 2.3 will handle complex expansion)
  // For now, just store the body text
  macro_def->SetDefinitionText(uvm_def->body);
  
  return macro_def;
}
```

**Status**: ⏳ TODO

---

### Step 4: Integrate into Macro Lookup Flow

**File**: `verible/verilog/preprocessor/verilog-preprocess.cc`

**Action**: Modify `HandleMacroIdentifier()` to check UVM registry

**Current Flow** (pseudocode):
```cpp
absl::Status HandleMacroIdentifier(...) {
  std::string_view macro_name = GetMacroName(token);
  
  // Look up in user-defined macros
  auto* user_macro = FindInUserMacros(macro_name);
  if (user_macro) {
    ExpandMacro(user_macro);
    return absl::OkStatus();
  }
  
  // Macro not found - error
  return absl::InvalidArgumentError("Undefined macro");
}
```

**New Flow**:
```cpp
absl::Status HandleMacroIdentifier(...) {
  std::string_view macro_name = GetMacroName(token);
  
  // Priority 1: User-defined macros (user can override UVM)
  auto* user_macro = FindInUserMacros(macro_name);
  if (user_macro) {
    ExpandMacro(user_macro);
    return absl::OkStatus();
  }
  
  // Priority 2: UVM built-in macros (NEW)
  auto uvm_macro = LookupUVMMacro(macro_name);
  if (uvm_macro) {
    ExpandMacro(*uvm_macro);
    return absl::OkStatus();
  }
  
  // Macro not found - error
  return absl::InvalidArgumentError("Undefined macro");
}
```

**Status**: ⏳ TODO

---

### Step 5: Add Configuration Flag (Optional Enhancement)

**File**: `verible/verilog/preprocessor/verilog-preprocess.h`

**Action**: Add flag to enable/disable UVM macros

```cpp
struct Config {
  bool filter_branches = false;
  bool include_files = false;
  bool expand_macros = false;
  bool enable_uvm_macros = true;  // NEW: Enable UVM built-in macros (default: true)
};
```

**Benefit**: Allows disabling UVM macros if conflicts arise

**Status**: ⏳ OPTIONAL (can defer to later phase)

---

## Phase 2.2 Testing Strategy

### Test 1: UVM Macro Recognition

**File**: Create `verible/verilog/preprocessor/verilog-preprocess-uvm_test.cc`

```cpp
TEST(VerilogPreprocessUVM, RecognizesUVMMacro) {
  const std::string code = R"(
    class test_item;
      `uvm_object_utils(test_item)
    endclass
  )";
  
  VerilogPreprocess::Config config;
  config.expand_macros = true;
  VerilogPreprocess preprocessor(config);
  
  auto data = preprocessor.ScanStream(LexCode(code));
  
  // Should not have "undefined macro" error
  EXPECT_TRUE(data.errors.empty());
}
```

### Test 2: User Override Priority

```cpp
TEST(VerilogPreprocessUVM, UserMacroOverridesUVM) {
  const std::string code = R"(
    `define uvm_info MY_CUSTOM_INFO
    
    class test;
      `uvm_info("test", "msg", UVM_LOW)
    endclass
  )";
  
  // User's `uvm_info should take precedence over built-in
  // Verify expansion uses user's definition, not UVM's
}
```

### Test 3: UVM Macro Not Found in User Macros

```cpp
TEST(VerilogPreprocessUVM, UVMMacroUsedWhenNotDefinedByUser) {
  const std::string code = R"(
    class test_item;
      `uvm_object_utils_begin(test_item)
      `uvm_object_utils_end
    endclass
  )";
  
  // UVM macros should be found and expanded
  EXPECT_NO_ERRORS();
}
```

### Test 4: Non-UVM Macro Still Errors

```cpp
TEST(VerilogPreprocessUVM, NonUVMMacroStillErrors) {
  const std::string code = R"(
    class test;
      `my_undefined_macro(arg)
    endclass
  )";
  
  // Should still get "undefined macro" error
  EXPECT_HAS_ERROR("Undefined macro: my_undefined_macro");
}
```

**Total Tests**: 4 integration tests (minimum for Phase 2.2)

---

## Known Limitations for Phase 2.2

### Limitation 1: Simplified Macro Expansion

**Issue**: UVM macro bodies in registry are simplified (essential functionality only)

**Impact**: Complex UVM patterns may not expand correctly yet

**Mitigation**: Phase 2.3 will enhance argument parsing and expansion

**Example**:
- Current: `uvm_object_utils_begin` expands to ~10 lines
- Full UVM: Should expand to ~50 lines
- For Phase 2.2: Simplified version is sufficient for parser tests

### Limitation 2: No Recursive Expansion Yet

**Issue**: Nested macro calls (e.g., `` `uvm_field_int`` inside `` `uvm_object_utils_begin``) not fully handled

**Impact**: Some complex UVM patterns won't parse

**Mitigation**: Phase 2.4 will implement recursive expansion

### Limitation 3: Argument Parsing is Basic

**Issue**: Complex arguments like `MyClass#(T1, T2)` may not parse correctly

**Impact**: Parameterized class registration may fail

**Mitigation**: Phase 2.3 will enhance argument parsing

---

## Success Criteria for Phase 2.2

| Criterion | Target | How to Verify |
|-----------|--------|---------------|
| UVM macros recognized | ≥29 macros | Unit tests pass |
| User override works | 100% | Priority test passes |
| No regressions | 0 failures | Existing preprocessor tests pass |
| Integration tests pass | 4/4 | New UVM preprocessor tests pass |
| BUILD compiles | Success | `bazel build //verible/verilog/preprocessor:all` |

---

## Risks & Mitigations

### Risk 1: MacroDefinition Conversion

**Issue**: Our `UVMMacroDef` structure differs from `verible::MacroDefinition`

**Impact**: Conversion might lose information or fail

**Mitigation**:
- Study `verible::MacroDefinition` API carefully
- Test conversion with simple cases first
- Document any limitations

**Fallback**: Store macro text as-is, defer expansion to parser

### Risk 2: Performance Overhead

**Issue**: Checking UVM registry on every macro lookup

**Impact**: Could slow down preprocessing

**Mitigation**:
- UVM registry uses `std::map` (O(log n) lookup)
- Only checked if user macro not found
- Negligible overhead expected (<1% performance impact)

**Measurement**: Benchmark before/after on large file

### Risk 3: Conflicts with User Macros

**Issue**: User might define macro with same name as UVM macro

**Impact**: Unexpected behavior if priority wrong

**Mitigation**:
- **User macros ALWAYS take precedence** (by design)
- Document this behavior clearly
- Add test to verify priority

**Status**: LOW RISK (intentional design)

---

## Timeline

**Week 4 Schedule**:

| Day | Tasks | Deliverables |
|-----|-------|--------------|
| Mon | Steps 1-2: Add dependency, include header | BUILD updated |
| Tue | Step 3: Implement `LookupUVMMacro()` | Helper method |
| Wed | Step 4: Integrate into macro lookup flow | Core integration |
| Thu | Step 5: Write integration tests | 4 tests |
| Fri | Run tests, fix issues, document | Phase 2.2 complete |

**Total Effort**: 5 days (1 week)

---

## Next Steps (Immediate Actions)

1. ✅ **Complete**: Update BUILD file with `uvm-macros` dependency
2. ⏳ **TODO**: Add `#include "uvm-macros.h"` to `verilog-preprocess.cc`
3. ⏳ **TODO**: Implement `LookupUVMMacro()` helper method
4. ⏳ **TODO**: Find and modify `HandleMacroIdentifier()` method
5. ⏳ **TODO**: Create `verilog-preprocess-uvm_test.cc` with 4 tests
6. ⏳ **TODO**: Run tests and verify no regressions

---

## Dependencies

**Prerequisites** (COMPLETE ✅):
- Phase 2.1: UVM Macro Registry ✅
- BUILD system integration ✅
- 15/15 registry tests passing ✅

**Blocks** (What Phase 2.2 enables):
- Phase 2.3: Argument Parsing (needs preprocessor integration)
- Phase 2.4: Recursive Expansion (needs preprocessor integration)
- Phase 2.5: Parser Tests (needs working UVM macros)

---

## Reference Files

### To Modify
1. `verible/verilog/preprocessor/BUILD` - Add dependency
2. `verible/verilog/preprocessor/verilog-preprocess.cc` - Core integration
3. `verible/verilog/preprocessor/verilog-preprocess.h` - (Optional) Add config flag

### To Create
4. `verible/verilog/preprocessor/verilog-preprocess-uvm_test.cc` - Integration tests

### To Reference
5. `verible/verilog/preprocessor/uvm-macros.h` - UVM registry API
6. `verible/common/text/macro-definition.h` - Verible's MacroDefinition class

---

## Conclusion

Phase 2.2 is well-scoped and ready for implementation. The architecture is clear, risks are identified, and a comprehensive test strategy is in place.

**Key Achievement**: After Phase 2.2, Verible will recognize UVM macros during preprocessing, enabling the parser to work with UVM constructs!

---

**Status**: Ready to Begin Phase 2.2 Implementation ⏳  
**Estimated Completion**: End of Week 4  
**Confidence**: HIGH (clear architecture, simple integration point)

---

*TDD approach: No hurry, no skip, chasing perfection!* 🎯  
*Next milestone: Preprocessor recognizes UVM macros!* 🚀

