# Deep Nesting Fix - Implementation Plan

**Date**: 2025-03-14  
**Issue**: Include files with 3+ levels don't fully expand macros  
**Impact**: 14 OpenTitan files (0.7%)  
**Goal**: 100% - No known issues

---

## 🎯 Problem Statement

### Current Behavior:
```
file.sv:
  `include "a.svh"     // Level 1
  constraint c {
    `MACRO(x)          // FAILS - macro not found
  }

a.svh:
  `include "b.svh"     // Level 2

b.svh:
  `include "c.svh"     // Level 3

c.svh:
  `define MACRO(x) x inside {[1:10]}  // Level 4 - TOO DEEP!
```

**Why it fails**: The preprocessor doesn't fully process nested includes before returning to parent context.

---

## 🔍 Root Cause Analysis

### Current Implementation:

1. ✅ `IncludeFileResolver` finds and caches files
2. ✅ `FileOpener` lambda returns file contents
3. ❌ **GAP**: File contents are NOT preprocessed before use
4. ❌ **GAP**: Macros from nested includes don't propagate up

### The Fix:

**Recursive Preprocessing**: When including a file, preprocess it FIRST, then return the preprocessed content.

```cpp
// CURRENT (Wrong):
FileOpener returns raw file content
→ Parent includes raw content
→ Macros from nested includes not defined

// NEEDED (Correct):
FileOpener preprocesses file recursively
→ All nested includes resolved
→ All macros defined
→ Return fully preprocessed content
→ Parent can use all macros
```

---

## 📋 Implementation Plan

### Phase 1: Refactor FileOpener (2-3 hours)

**Current**:
```cpp
using FileOpener = std::function<absl::StatusOr<std::string_view>(std::string_view)>;
```

**Problem**: Returns raw file content (no preprocessing)

**Solution**: Make FileOpener preprocessing-aware

**Options**:

**Option A: Change FileOpener signature** (Breaking change)
```cpp
using FileOpener = std::function<
  absl::StatusOr<std::string_view>(
    std::string_view filename,
    VerilogPreprocess* preprocessor  // ← NEW: for recursive preprocessing
  )>;
```

**Option B: Add PreprocessingFileOpener** (Backward compatible)
```cpp
// Keep existing FileOpener for simple cases
using FileOpener = std::function<absl::StatusOr<std::string_view>(std::string_view)>;

// Add new preprocessing-aware opener
using PreprocessingFileOpener = std::function<
  absl::StatusOr<std::string_view>(
    std::string_view filename,
    const std::map<std::string, MacroDefinition>& current_macros,
    PreprocessingFileOpener* self  // For recursion
  )>;
```

**Option C: Separate PreprocessInclude method** (Cleanest)
```cpp
class VerilogPreprocess {
  // Existing method for simple file loading
  absl::StatusOr<std::string_view> LoadIncludeFile(std::string_view filename);
  
  // NEW: Recursively preprocess an include file
  absl::StatusOr<std::string> PreprocessIncludeFile(std::string_view filename);
};
```

**Recommendation**: **Option C** - cleanest separation of concerns

---

### Phase 2: Implement Recursive Preprocessing (3-4 hours)

**New Method in VerilogPreprocess**:

```cpp
absl::StatusOr<std::string> VerilogPreprocess::PreprocessIncludeFile(
    std::string_view filename) {
  
  // 1. Check circular includes (use existing stack)
  if (IsInIncludeStack(filename)) {
    return absl::InvalidArgumentError(
        absl::StrCat("Circular include detected: ", filename));
  }
  
  // 2. Load raw file content
  if (!file_opener_) {
    return absl::InvalidArgumentError("No file opener configured");
  }
  
  auto raw_content = file_opener_(filename);
  if (!raw_content.ok()) {
    return raw_content.status();
  }
  
  // 3. Push onto include stack
  PushIncludeStack(filename);
  
  // 4. Create NEW preprocessor instance for this file
  //    (inherits parent's macro definitions + config)
  VerilogPreprocess nested_preprocessor(config_, file_opener_);
  
  // 5. Copy parent's macro definitions to nested preprocessor
  nested_preprocessor.preprocess_data_.macro_definitions = 
      preprocess_data_.macro_definitions;
  
  // 6. Recursively preprocess the included file
  auto preprocessed = nested_preprocessor.ScanAndPreprocess(*raw_content);
  if (!preprocessed.ok()) {
    PopIncludeStack();
    return preprocessed.status();
  }
  
  // 7. Merge new macro definitions back to parent
  for (const auto& [name, def] : 
       nested_preprocessor.preprocess_data_.macro_definitions) {
    if (!preprocess_data_.macro_definitions.count(name)) {
      preprocess_data_.macro_definitions[name] = def;
    }
  }
  
  // 8. Pop include stack
  PopIncludeStack();
  
  // 9. Return preprocessed content
  return std::string(preprocessed->text());
}
```

**Key Points**:
- ✅ Circular include detection (reuse existing stack)
- ✅ Recursive preprocessing (nested VerilogPreprocess instance)
- ✅ Macro propagation (merge definitions back to parent)
- ✅ Config inheritance (nested preprocessor uses same config)
- ✅ Error handling (proper status returns)

---

### Phase 3: Integrate with Include Directive Handler (1-2 hours)

**Find where `include directives are processed**:

```bash
grep -n "PP_include\|include.*directive" verible/verilog/preprocessor/verilog-preprocess.cc
```

**Current (likely)**:
```cpp
case TK_PP_include:
  // Load file
  auto content = file_opener_(filename);
  // Insert raw content into token stream
  InsertTokens(content);
  break;
```

**New**:
```cpp
case TK_PP_include:
  if (config_.expand_macros && config_.include_files) {
    // Recursively preprocess
    auto preprocessed = PreprocessIncludeFile(filename);
    if (preprocessed.ok()) {
      InsertTokens(*preprocessed);
    } else {
      // Error handling
      preprocess_data_.errors.push_back(...);
    }
  } else {
    // Fallback to raw content (backward compatible)
    auto content = file_opener_(filename);
    InsertTokens(content);
  }
  break;
```

---

### Phase 4: Update IncludeFileResolver (1 hour)

**Current**: Returns raw file content  
**Needed**: Support recursive preprocessing

**Changes**:
```cpp
class IncludeFileResolver {
 public:
  // Existing method - keep for backward compatibility
  absl::StatusOr<std::string_view> ResolveInclude(
      std::string_view include_file,
      std::string_view current_file = "");
  
  // NEW: Get file opener that supports preprocessing
  FileOpener GetFileOpener() const;
  
 private:
  // Cache for RAW files (existing)
  std::map<std::string, std::shared_ptr<verible::MemBlock>> cached_files_;
  
  // NEW: Cache for PREPROCESSED files
  std::map<std::string, std::shared_ptr<std::string>> preprocessed_cache_;
};
```

---

### Phase 5: Testing (2-3 hours)

**Test 1: Basic Recursive Include**
```cpp
TEST(DeepNesting, ThreeLevels) {
  // c.svh: `define MACRO(x) x inside {[1:10]}
  // b.svh: `include "c.svh"
  // a.svh: `include "b.svh"
  // test.sv: `include "a.svh"
  //          constraint c { `MACRO(x) }
  
  EXPECT_TRUE(ParsesSuccessfully(test_sv));
}
```

**Test 2: Macro Propagation**
```cpp
TEST(DeepNesting, MacroPropagation) {
  // Verify macros from deeply nested files are available
  // in parent context
}
```

**Test 3: Circular Include Detection**
```cpp
TEST(DeepNesting, CircularDetection) {
  // a.svh includes b.svh
  // b.svh includes a.svh
  EXPECT_FALSE(ParsesSuccessfully(...));
}
```

**Test 4: Performance**
```cpp
TEST(DeepNesting, Performance) {
  // 10-level deep includes should complete in < 1 second
}
```

**Test 5: OpenTitan Validation**
```bash
# Test the 14 failing files
./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax \
  --include_paths=... \
  --preprocess=true \
  cip_base_env_cfg.sv

# Expected: SUCCESS ✅
```

---

## 📊 Expected Results

### Before Fix:
- ✅ Simple includes (1-2 levels): Work
- ❌ Deep includes (3+ levels): Fail
- **OpenTitan**: 2,094 / 2,108 (99.3%)

### After Fix:
- ✅ Simple includes (1-2 levels): Work
- ✅ Deep includes (3+ levels): Work
- **OpenTitan**: 2,108 / 2,108 (100%) ✅

---

## ⏰ Timeline

| Phase | Task | Time | Status |
|-------|------|------|--------|
| 1 | Refactor FileOpener | 2-3h | ⏸️ Pending |
| 2 | Recursive preprocessing | 3-4h | ⏸️ Pending |
| 3 | Integration | 1-2h | ⏸️ Pending |
| 4 | Update resolver | 1h | ⏸️ Pending |
| 5 | Testing | 2-3h | ⏸️ Pending |
| **Total** | **Complete fix** | **9-13h** | ⏸️ |

**Estimated**: 1-2 days of focused work

---

## 🎯 Success Criteria

1. ✅ All 10 deep nesting tests pass
2. ✅ Zero regressions (existing tests still pass)
3. ✅ OpenTitan: 2,108/2,108 (100%)
4. ✅ Performance: < 1 second for 10-level nesting
5. ✅ Memory: < 50 MB for typical projects

---

## 🚀 Implementation Order

### Step 1: Create Tests (TDD Red) - 1 hour
```bash
# Create test file
cat > verible/verilog/preprocessor/verilog-preprocess-deep-nesting_test.cc << 'EOF'
// 5 tests for deep nesting
EOF

# Add to BUILD
# Run tests - expect FAIL
```

### Step 2: Implement PreprocessIncludeFile - 3-4 hours
```cpp
// Add method to verilog-preprocess.h
// Implement in verilog-preprocess.cc
// Handle recursion, macro propagation
```

### Step 3: Integrate with Include Handler - 1-2 hours
```cpp
// Find TK_PP_include case
// Call PreprocessIncludeFile
// Test integration
```

### Step 4: Run Tests (TDD Green) - 1 hour
```bash
# Run deep nesting tests
# Expected: 5/5 PASS
```

### Step 5: OpenTitan Validation - 1 hour
```bash
# Test all 2,108 files
# Expected: 100% pass rate
```

---

## 💡 Alternative Approaches

### Alternative 1: Multi-Pass Preprocessing
**Idea**: Preprocess parent multiple times until all includes resolved  
**Pro**: Simpler implementation  
**Con**: Inefficient (O(n²) for n levels)  
**Verdict**: ❌ Not recommended

### Alternative 2: Flatten All Includes First
**Idea**: Recursively load all includes, then preprocess once  
**Pro**: Single preprocessing pass  
**Con**: Complex dependency tracking  
**Verdict**: ⚠️ Possible but complex

### Alternative 3: Recursive Preprocessing (RECOMMENDED)
**Idea**: Preprocess each include file recursively  
**Pro**: Clean, efficient, correct  
**Con**: Requires careful macro scope management  
**Verdict**: ✅ **BEST APPROACH**

---

## 🎓 Key Design Decisions

### Decision 1: How to handle macro scope?
**Answer**: Copy parent macros to child, merge child macros back to parent

### Decision 2: How to prevent infinite recursion?
**Answer**: Reuse existing include stack tracking

### Decision 3: How to cache preprocessed files?
**Answer**: Separate cache for preprocessed content

### Decision 4: Backward compatibility?
**Answer**: Keep existing FileOpener, add PreprocessIncludeFile method

---

## ✅ Acceptance Criteria

### Code Quality:
- ✅ No breaking changes to existing APIs
- ✅ Clear separation of concerns
- ✅ Comprehensive error handling
- ✅ Well-documented code

### Functionality:
- ✅ Deep nesting works (3+ levels)
- ✅ Circular includes detected
- ✅ Macro propagation correct
- ✅ Zero regressions

### Performance:
- ✅ < 1 second for 10-level nesting
- ✅ < 50 MB memory overhead
- ✅ File caching still works

### Testing:
- ✅ 5 new deep nesting tests
- ✅ All existing tests still pass
- ✅ OpenTitan: 100% pass rate

---

## 🚀 Ready to Implement

**Next Action**: Create deep nesting test file (TDD Red)

**Command**:
```bash
# Start with tests
cat > verible/verilog/preprocessor/verilog-preprocess-deep-nesting_test.cc
```

**Timeline**: 1-2 days to 100% OpenTitan

**Goal**: NO KNOWN ISSUES ✅

---

**Status**: Plan complete, ready to implement  
**Confidence**: HIGH (clear path to 100%)  
**Estimated**: 9-13 hours total work

