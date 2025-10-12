# Phase A & B Checkpoint - Advanced Metadata Implementation

## Session Status: Checkpoint for Resume

**Date:** October 12, 2025  
**Branch:** `veripg/phases-9-22-enhancements`  
**Context Window:** Ready for fresh start

---

## What Happened

### ✅ Completed Before Loss:
1. **Session 1: Location Tracking** - Fully implemented and tested
   - Test 12 (ForwardTypedefReferences) was **PASSING**
   - Location tracking (line/column) fully functional
   - Forward reference detection working

### ❌ Lost in Git Checkout:
- ~1,200 lines of Phase A implementation
- All typedef resolution code
- Location tracking implementation
- Test 12 solution

### ✅ Still Present:
- All 15 Phase A tests (compiled, failing)
- All 12 Phase B tests (compiled, failing)
- Complete documentation and roadmap
- Clear implementation plan

---

## Current Test Status

**Phase A:** 0/15 tests passing (implementation lost)
- Tests 1-15 exist and compile
- Need complete re-implementation

**Phase B:** 0/12 tests passing (not yet implemented)
- Test suite exists and compiles
- Ready for implementation after Phase A

---

## Implementation Strategy for Next Session

### Step 1: Add Dependencies & Includes (~5 min)

**File:** `verible/verilog/CST/verilog-tree-json.cc`

**Add to includes:**
```cpp
#include <functional>
#include <iostream>
#include <regex>
#include <vector>

#include "verible/verilog/CST/identifier.h"
#include "verible/verilog/CST/type.h"
#include "verible/verilog/CST/declaration.h"
#include "verible/verilog/CST/verilog-matchers.h"
```

**Add to BUILD file:**
```python
deps = [
    ":identifier",
    ":type",
    ":declaration",
    ":verilog-matchers",
]
```

### Step 2: TypedefInfo Struct (~10 min)

**Location:** After `AddLocationMetadata()` function (~line 480)

```cpp
// Forward declarations for typedef resolution
struct TypedefInfo {
  std::string typedef_name;
  std::string base_type;  // e.g., "logic", "bit"
  int width;
  bool is_signed;
  bool is_packed;
  bool is_enum;
  int enum_member_count;
  bool is_struct;
  int struct_field_count;
  std::vector<std::string> struct_field_names;
  bool is_union;
  int union_member_count;
  bool is_parameterized;
  bool is_array;
  int array_dimensions;
  std::vector<int> dimension_sizes;
  int resolution_depth;
  int definition_line;
  int definition_column;
  std::string dimension_string;
  std::string resolved_type_string;
};
```

### Step 3: BuildTypedefTable Function (~60 min)

**Core logic:**
1. Search for all `kTypeDeclaration` nodes
2. Extract typedef name, base type, dimensions
3. Handle enum/struct/union types
4. Resolve typedef chains recursively
5. Extract source location (line/column)
6. Handle package-scoped typedefs

**Key functions to use:**
- `verible::SearchSyntaxTree(root, NodekTypeDeclaration())`
- `GetSubtreeAsSymbol(node, NodeEnum::kTypeDeclaration, index)`
- `GetBaseTypeFromDataType(*ref_type)`
- `verible::StringSpanOfSymbol(node)` for location

**Recursive resolution lambda:**
```cpp
std::function<TypedefInfo(const std::string&)> resolve_typedef_chain;
resolve_typedef_chain = [&](const std::string& name) -> TypedefInfo {
  auto it = typedef_table.find(name);
  if (it == typedef_table.end()) return {};
  
  TypedefInfo info = it->second;
  if (/* base_type is another typedef */) {
    TypedefInfo resolved = resolve_typedef_chain(info.base_type);
    // Copy resolved metadata
    info.resolution_depth = resolved.resolution_depth + 1;
  }
  return info;
};
```

### Step 4: AddTypeResolutionMetadata Function (~40 min)

**Purpose:** Enrich `kDataDeclaration` nodes with type metadata

**Logic:**
1. Extract declared type from `kInstantiationBase` → `kDataType`
2. Look up in typedef_table
3. Detect forward references (usage_line < definition_line)
4. Handle package-scoped types (`my_pkg::word_t`)
5. Add `type_info` to JSON metadata

**Metadata structure:**
```json
{
  "metadata": {
    "type_info": {
      "declared_type": "byte_t",
      "resolved_type": "logic [7:0]",
      "is_typedef": true,
      "base_type": "logic",
      "width": 8,
      "signed": false,
      "packed": true,
      "is_forward_reference": false,
      "definition_location": {"line": 5, "column": 3},
      "resolution_depth": 1
    }
  }
}
```

### Step 5: Package Symbol Table (~30 min)

**Enhancement to BuildTypedefTable:**
1. Find all `kPackageDeclaration` nodes
2. Extract package name
3. Find typedefs within package
4. Store with qualified names (`my_pkg::word_t`)

**Key function:**
```cpp
auto package_matches = verible::SearchSyntaxTree(root, NodekPackageDeclaration());
for (const auto& pkg_match : package_matches) {
  // Extract package name
  // Find typedefs in package
  // Store as "pkg_name::typedef_name"
}
```

### Step 6: Integration (~20 min)

**File:** `verilog-tree-json.cc`

**Modify:**
1. `VerilogTreeToJsonConverter` constructor - accept typedef_table
2. `Visit(SyntaxTreeNode)` - call `AddTypeResolutionMetadata` for `kDataDeclaration`
3. `ConvertVerilogTreeToJson` - call `BuildTypedefTable` and pass to converter

### Step 7: Test & Commit (~30 min)

**Run tests:**
```bash
bazel-bin/.../verilog-tree-json-type-resolution_test
```

**Target:**
- Tests 1-11: Pass (core typedef resolution)
- Test 12: Pass (forward references with location tracking)
- Test 13: Pass (package-scoped typedefs)
- Tests 14-15: Pass (negative test, performance)

**Expected:** 15/15 tests passing (100%)

**CRITICAL: Commit immediately after passing!**
```bash
git add verible/verilog/CST/
git commit -m "feat: Phase A Type Resolution Metadata (15/15 tests, 100%)"
```

---

## Phase B: Cross-Reference Metadata (Next)

### After Phase A 100%, implement:

**SymbolInfo struct:**
```cpp
struct SymbolInfo {
  std::string symbol_name;
  std::string symbol_type;  // "variable" | "port" | "parameter"
  bool is_definition;
  int line;
  int column;
  std::string scope;
  bool is_input;
  bool is_output;
  bool is_inout;
  bool is_parameter;
};
```

**BuildSymbolTable function:**
- Traverse CST for `kDataDeclaration`, `kPortDeclaration`, `kParamDeclaration`
- Track definitions vs usages
- Return `std::unordered_map<std::string, std::vector<SymbolInfo>>`

**AddCrossReferenceMetadata function:**
- Look up symbol in symbol_table
- Determine if definition or usage
- Add `cross_ref` metadata

**Integration:**
- Modify `Visit()` to call for `kReference`, `kUnqualifiedId`
- Pass symbol_table through converter

---

## Code Templates Ready to Use

### Template 1: Location Extraction

```cpp
// Extract source location from node
std::string_view node_text = verible::StringSpanOfSymbol(node);
if (!source_text.empty() && node_text.data() >= source_text.data() && 
    node_text.data() < source_text.data() + source_text.size()) {
  size_t offset = node_text.data() - source_text.data();
  int line = 1, column = 1;
  for (size_t i = 0; i < offset && i < source_text.size(); ++i) {
    if (source_text[i] == '\n') {
      line++;
      column = 1;
    } else {
      column++;
    }
  }
  info.definition_line = line;
  info.definition_column = column;
}
```

### Template 2: Enum Detection

```cpp
if (base_node.MatchesTag(NodeEnum::kDataTypePrimitive)) {
  const verible::Symbol* prim_child = GetSubtreeAsSymbol(base_node, NodeEnum::kDataTypePrimitive, 0);
  if (prim_child && prim_child->Kind() == verible::SymbolKind::kNode) {
    const auto& prim_child_node = verible::SymbolCastToNode(*prim_child);
    if (prim_child_node.MatchesTag(NodeEnum::kEnumType)) {
      info.is_enum = true;
      // Extract enum members...
    }
  }
}
```

### Template 3: Struct Detection

```cpp
if (prim_child_node.MatchesTag(NodeEnum::kStructType)) {
  info.is_struct = true;
  
  // Check for packed keyword
  const verible::Symbol* signing = GetSubtreeAsSymbol(base_node, NodeEnum::kDataTypePrimitive, 1);
  if (signing) {
    const auto& signing_node = verible::SymbolCastToNode(*signing);
    if (signing_node.MatchesTag(NodeEnum::kPackedSigning)) {
      // packed struct
      info.is_packed = true;
    }
  }
  
  // Extract struct fields...
}
```

---

## Quick Start for Next Session

### Commands to Run:

```bash
# 1. Ensure correct branch
cd /Users/jonguksong/Projects/verible
git checkout veripg/phases-9-22-enhancements

# 2. Verify test suite compiles
bazel build //verible/verilog/CST:verilog-tree-json-type-resolution_test --macos_minimum_os=10.15

# 3. Run tests (should all fail initially)
bazel-bin/verible/verilog/CST/verilog-tree-json-type-resolution_test

# 4. Start implementation
# - Open verilog-tree-json.cc
# - Add includes (Step 1)
# - Add TypedefInfo struct (Step 2)
# - Implement BuildTypedefTable (Step 3)
# - etc.

# 5. Test incrementally
bazel build //verible/verilog/CST:verilog-tree-json-type-resolution_test --macos_minimum_os=10.15
bazel-bin/verible/verilog/CST/verilog-tree-json-type-resolution_test --gtest_filter="TypeResolutionTest.SimpleTypedef"

# 6. COMMIT after each milestone!
git add verible/verilog/CST/
git commit -m "feat: Phase A Type Resolution - Tests 1-5 passing"
```

---

## Success Metrics

**Phase A Complete:**
- ✅ 15/15 tests passing (100%)
- ✅ Code committed to branch
- ✅ Location tracking working
- ✅ Package-scoped typedefs resolved

**Phase B Complete:**
- ✅ 12/12 tests passing (100%)
- ✅ Symbol table infrastructure
- ✅ Cross-reference metadata

**Combined:**
- ✅ 27/27 tests passing (100%)
- ✅ 100% typedef resolution on OpenTitan
- ✅ Full advanced metadata support

---

## Estimated Time for Next Session

**Phase A Re-implementation:** 2-3 hours
- Step 1-2: 15 min (setup)
- Step 3: 60 min (BuildTypedefTable)
- Step 4: 40 min (AddTypeResolutionMetadata)
- Step 5: 30 min (Package support)
- Step 6: 20 min (Integration)
- Step 7: 30 min (Test & commit)

**Phase B Implementation:** 3-4 hours
- Symbol table infrastructure
- Cross-reference metadata
- 12 tests

**Total to 100%:** 5-7 hours of focused work

---

## Resume Point

**When resuming:**
1. Read this checkpoint document
2. Review `doc/PHASE_B_IMPLEMENTATION_ROADMAP.md`
3. Follow Step 1-7 sequentially
4. Commit after each major milestone
5. Proceed to Phase B after Phase A 100%

**Files to edit:**
- `verible/verilog/CST/verilog-tree-json.cc` (main implementation)
- `verible/verilog/CST/verilog-tree-json.h` (declarations)
- `verible/verilog/CST/BUILD` (dependencies)

**Test files (already exist):**
- `verible/verilog/CST/verilog-tree-json-type-resolution_test.cc` (15 tests)
- `verible/verilog/CST/verilog-tree-json-cross-reference_test.cc` (12 tests)

---

**Status:** Checkpoint complete. Ready for fresh implementation session with clear roadmap to 100%.

