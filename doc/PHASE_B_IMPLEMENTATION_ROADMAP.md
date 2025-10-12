# Phase B Implementation Roadmap: Achieving 100% Type Resolution

## Current Status

**Phase A: 13/15 tests passing (86.7%)**
- ✅ Tests 1-11: All core typedef resolution
- ✅ Test 14: UnresolvedTypedef
- ✅ Test 15: Performance100NestedTypedefs
- ❌ Test 12: ForwardTypedefReferences - **Needs location tracking**
- ❌ Test 13: PackageScopedTypedef - **Needs package symbol table**

**Phase B: 0/12 tests passing (0%)**
- All 12 tests failing (TDD RED phase ✅)
- Test suite compiles successfully
- Ready for implementation

---

## Path to 100%: Two Critical Features

### Feature 1: Source Location Tracking
**Solves:** Phase A Test 12 (Forward References)  
**Impact:** 96.2% → 100% coverage (fixes 100 forward references)

**Implementation:**

```cpp
// 1. Add location fields to TypedefInfo
struct TypedefInfo {
  // ... existing fields ...
  int definition_line;
  int definition_column;
};

// 2. Extract location in BuildTypedefTable()
const auto* typedef_node = /* find kTypeDeclaration */;
const verible::LineColumnRange location = typedef_node->GetLineColumnRange();
info.definition_line = location.start.line;
info.definition_column = location.start.column;

// 3. Check forward reference in AddTypeResolutionMetadata()
const verible::LineColumnRange usage_location = node.GetLineColumnRange();
if (usage_location.start.line < info.definition_line) {
  // Usage BEFORE definition = forward reference
  type_info["is_forward_reference"] = true;
} else {
  type_info["is_forward_reference"] = false;
}

// 4. Still resolve the typedef!
type_info["resolved_type"] = info.resolved_type_string;
type_info["definition_location"] = {
  {"line", info.definition_line},
  {"column", info.definition_column}
};
```

**Test Verification:**
```systemverilog
module test;
  initial begin
    data = 1'b1;    // Line 4: usage BEFORE definition
  end
  
  logic data;       // Line 7: definition AFTER usage
endmodule

// Expected:
// {"is_forward_reference": true, "resolved_type": "logic", "definition_location": {"line": 7}}
```

---

### Feature 2: Global Package Symbol Table
**Solves:** Phase A Test 13 (Package-Scoped Types)  
**Impact:** 96.2% → 100% coverage (fixes 52 package-scoped types)

**Implementation:**

```cpp
// 1. Modify BuildTypedefTable to accept scope parameter
static std::unordered_map<std::string, TypedefInfo> BuildTypedefTable(
    const verible::Symbol& root, 
    const std::string& scope_prefix = ""
) {
  std::unordered_map<std::string, TypedefInfo> typedef_table;
  
  // Find all packages in the tree
  auto packages = FindAllMatching(root, NodekMatches(NodeEnum::kPackageDeclaration));
  
  for (const auto& package : packages) {
    // Extract package name
    const std::string pkg_name = /* extract from kPackageDeclaration */;
    
    // Build typedefs within this package
    auto pkg_typedefs = BuildTypedefTableInternal(package, pkg_name + "::");
    
    // Add to global table with qualified names
    for (auto& [name, info] : pkg_typedefs) {
      // Add qualified: "my_pkg::word_t"
      typedef_table[pkg_name + "::" + name] = info;
      info.package_name = pkg_name;
      info.is_package_scoped = true;
    }
  }
  
  // Also process module-level typedefs (no scope prefix)
  auto module_typedefs = BuildTypedefTableInternal(root, "");
  typedef_table.insert(module_typedefs.begin(), module_typedefs.end());
  
  return typedef_table;
}

// 2. Handle package-scoped lookup in AddTypeResolutionMetadata()
// (Already implemented in Phase A - just needs global table!)
if (declared_type.find("::") != std::string::npos) {
  auto it = typedef_table.find(declared_type);  // Now finds "my_pkg::word_t"
  if (it != typedef_table.end()) {
    type_info["resolved_type"] = it->second.resolved_type_string;
    type_info["is_package_scoped"] = true;
    type_info["package_name"] = it->second.package_name;
  }
}
```

**Test Verification:**
```systemverilog
package my_pkg;
  typedef logic [63:0] word_t;  // Stored as "my_pkg::word_t"
endpackage

module test;
  import my_pkg::*;
  my_pkg::word_t data;  // Looks up "my_pkg::word_t" in global table
endmodule

// Expected:
// {"declared_type": "my_pkg::word_t", "resolved_type": "logic [63:0]", 
//  "is_package_scoped": true, "package_name": "my_pkg"}
```

---

## Phase B: Cross-Reference Metadata Implementation

**Goal:** Add `cross_ref` metadata to track definitions vs usages

**New Infrastructure:**

```cpp
// 1. Symbol Table Structure
struct SymbolInfo {
  std::string symbol_name;
  std::string symbol_type;  // "variable" | "port" | "parameter" | "module" | "typedef"
  bool is_definition;
  verible::LineColumnRange location;
  std::string scope;
  
  // For ports
  bool is_input;
  bool is_output;
  bool is_inout;
  
  // For parameters
  bool is_parameter;
};

// 2. Build Symbol Table (Single Pass)
static std::unordered_map<std::string, std::vector<SymbolInfo>> BuildSymbolTable(
    const verible::Symbol& root
) {
  std::unordered_map<std::string, std::vector<SymbolInfo>> symbol_table;
  
  // Traverse tree and collect:
  // - kDataDeclaration → definitions
  // - kPortDeclaration → port definitions
  // - kParamDeclaration → parameter definitions
  // - kReference → usages
  // - kUnqualifiedId → identifier usages
  
  return symbol_table;
}

// 3. Add Cross-Reference Metadata
static void AddCrossReferenceMetadata(
    json& node_json,
    const verible::Symbol& node,
    const std::unordered_map<std::string, std::vector<SymbolInfo>>& symbol_table
) {
  // Extract symbol name from node
  std::string symbol_name = /* extract from kReference or kUnqualifiedId */;
  
  // Look up in symbol table
  auto it = symbol_table.find(symbol_name);
  if (it == symbol_table.end()) {
    // Unresolved reference
    json xref = {
      {"symbol", symbol_name},
      {"ref_type", "usage"},
      {"is_unresolved", true}
    };
    node_json["metadata"]["cross_ref"] = xref;
    return;
  }
  
  // Find definition
  const SymbolInfo* definition = nullptr;
  for (const auto& info : it->second) {
    if (info.is_definition) {
      definition = &info;
      break;
    }
  }
  
  // Determine if this node is definition or usage
  const verible::LineColumnRange node_location = node.GetLineColumnRange();
  bool is_definition_node = (definition && 
                             node_location.start.line == definition->location.start.line &&
                             node_location.start.column == definition->location.start.column);
  
  json xref = {
    {"symbol", symbol_name},
    {"ref_type", is_definition_node ? "definition" : "usage"}
  };
  
  if (definition) {
    xref["definition_location"] = {
      {"line", definition->location.start.line},
      {"column", definition->location.start.column}
    };
    xref["scope"] = definition->scope;
    
    // Add port/parameter flags
    if (definition->is_input || definition->is_output || definition->is_inout) {
      xref["is_input"] = definition->is_input;
      xref["is_output"] = definition->is_output;
      xref["is_inout"] = definition->is_inout;
    }
    if (definition->is_parameter) {
      xref["is_parameter"] = true;
    }
    
    // Check forward reference
    if (!is_definition_node && node_location.start.line < definition->location.start.line) {
      xref["is_forward_reference"] = true;
    }
  } else {
    xref["is_unresolved"] = true;
  }
  
  node_json["metadata"]["cross_ref"] = xref;
}

// 4. Integrate into VerilogTreeToJsonConverter::Visit()
void Visit(const SyntaxTreeLeaf& leaf) override {
  // ... existing code ...
  
  // Add cross-reference metadata for identifiers
  if (IsIdentifierLike(leaf.get().token_enum())) {
    AddCrossReferenceMetadata(result_[&leaf], leaf, symbol_table_);
  }
}

void Visit(const SyntaxTreeNode& node) override {
  // ... existing code ...
  
  // Add cross-reference metadata for references
  if (node.MatchesTag(NodeEnum::kReference) || 
      node.MatchesTag(NodeEnum::kDataDeclaration) ||
      node.MatchesTag(NodeEnum::kPortDeclaration) ||
      node.MatchesTag(NodeEnum::kParamDeclaration)) {
    AddCrossReferenceMetadata(result_[&node], node, symbol_table_);
  }
}
```

---

## Implementation Schedule (100% Completion)

### Session 1: Location Tracking (2-3 hours)
**Goal:** Phase A Test 12 → PASS

1. Add `definition_line`, `definition_column` to `TypedefInfo`
2. Extract location in `BuildTypedefTable()` using `GetLineColumnRange()`
3. Compare usage location vs definition location
4. Set `is_forward_reference` flag appropriately
5. **Verify:** `bazel-bin/.../verilog-tree-json-type-resolution_test --gtest_filter="*.ForwardTypedefReferences"` → PASS

### Session 2: Package Symbol Table (3-4 hours)
**Goal:** Phase A Test 13 → PASS

1. Modify `BuildTypedefTable()` to traverse packages
2. Extract package names from `kPackageDeclaration`
3. Store typedefs with qualified names (`pkg::type`)
4. Update lookup logic (already in place!)
5. **Verify:** `bazel-bin/.../verilog-tree-json-type-resolution_test --gtest_filter="*.PackageScopedTypedef"` → PASS
6. **MILESTONE:** Phase A 15/15 tests passing (100%)!

### Session 3: Symbol Table Infrastructure (4-5 hours)
**Goal:** Phase B Tests 1-4 → PASS

1. Create `SymbolInfo` struct
2. Implement `BuildSymbolTable()` function
3. Traverse CST to collect definitions
4. Track variable, port, parameter declarations
5. **Verify:** Tests 1-4 passing

### Session 4: Cross-Reference Integration (3-4 hours)
**Goal:** Phase B Tests 5-8 → PASS

1. Implement `AddCrossReferenceMetadata()` function
2. Integrate into `Visit()` methods
3. Handle hierarchical references
4. Detect forward references
5. **Verify:** Tests 5-8 passing

### Session 5: Advanced Cases (2-3 hours)
**Goal:** Phase B Tests 9-12 → PASS

1. Handle multiple definitions (redeclaration)
2. Track unresolved references
3. Implement package import tracking
4. Performance optimization for 500+ signals
5. **Verify:** All Phase B tests passing
6. **MILESTONE:** Phase B 12/12 tests passing (100%)!

### Session 6: Integration & Documentation (2 hours)
**Goal:** Complete 100% delivery

1. Run full test suite (Phase A + Phase B)
2. Verify performance on OpenTitan (1852 typedefs)
3. Update documentation
4. Create release notes
5. **FINAL:** 27/27 tests passing, 100% typedef resolution!

---

## Total Estimated Effort: 16-21 hours

**Breakdown:**
- Location Tracking: 2-3 hours → **96.2% coverage**
- Package Symbol Table: 3-4 hours → **100% coverage!** ✅
- Symbol Table Infrastructure: 4-5 hours
- Cross-Reference Integration: 3-4 hours
- Advanced Cases: 2-3 hours
- Integration & Docs: 2 hours

---

## Success Criteria for 100%

✅ **Phase A:** 15/15 tests passing (100%)
- Tests 1-11: Already passing
- Test 12: ForwardTypedefReferences → Pass with location tracking
- Test 13: PackageScopedTypedef → Pass with package symbol table
- Test 14: UnresolvedTypedef → Already passing
- Test 15: Performance100NestedTypedefs → Already passing

✅ **Phase B:** 12/12 tests passing (100%)
- All 12 cross-reference tests passing with symbol table

✅ **VeriPG Integration:** 1852/1852 typedefs resolved (100%)
- 1700 simple typedefs: ✅ Working
- 100 forward references: ✅ Fixed with location tracking
- 52 package-scoped types: ✅ Fixed with package symbol table

✅ **Performance:** <5% overhead on large files

✅ **Documentation:** Complete with examples

---

## Key Files to Modify

### For 100% Type Resolution:
```
verible/verilog/CST/verilog-tree-json.cc  (+200 lines)
  - Add location extraction to BuildTypedefTable()
  - Modify BuildTypedefTable() to handle packages
  - Update AddTypeResolutionMetadata() forward ref logic

verible/verilog/CST/verilog-tree-json.h   (+20 lines)
  - Add location fields to TypedefInfo
  - Add package_name, is_package_scoped fields
```

### For Phase B Cross-Reference:
```
verible/verilog/CST/verilog-tree-json.cc  (+400 lines)
  - struct SymbolInfo
  - BuildSymbolTable() function
  - AddCrossReferenceMetadata() function
  - Integrate into Visit() methods

verible/verilog/CST/verilog-tree-json.h   (+50 lines)
  - SymbolInfo struct declaration
  - Function declarations
```

---

## Next Session Action Plan

**Priority 1: Achieve 100% Type Resolution (Sessions 1-2)**

1. Start with location tracking (Test 12)
2. Add package symbol table (Test 13)
3. Verify Phase A 15/15 → **100% COMPLETE**

**Priority 2: Implement Phase B (Sessions 3-5)**

4. Build symbol table infrastructure
5. Add cross-reference metadata
6. Verify Phase B 12/12 → **100% COMPLETE**

**Priority 3: Deploy (Session 6)**

7. Full integration testing
8. Performance verification on OpenTitan
9. Documentation and release

---

## Commit Points

**Checkpoint 1:** After Session 2
- Phase A 100% complete
- 1852/1852 typedefs resolved
- Ready for VeriPG deployment

**Checkpoint 2:** After Session 5
- Phase A + Phase B 100% complete
- Full advanced metadata support
- v4.0 release candidate

---

**Status:** Ready to implement. All tests compiled and failing (TDD RED ✅).  
**Next Step:** Session 1 - Location Tracking for Test 12.

