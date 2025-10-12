# Phases B, C, D Implementation Plan

## Overview

**Current Status:** Phase A Complete (15/15 tests ✓)  
**Remaining:** Phase B (6/12 passing), Phase C (not started), Phase D (not started)  
**Goal:** Complete all phases and deploy to VeriPG

---

## Phase B: Cross-Reference Metadata (Target: 12/12 tests)

### Current Status: 6/12 tests passing (50%)

**Passing Tests:**
- CrossModuleReference
- DefinitionBeforeUse
- ForwardReference
- MultipleDefinitions
- UnresolvedReference
- PackageImportReference

**Failing Tests (Need Implementation):**
- SimpleVariableDefinitionUsage
- PortDefinitions
- ParameterDefinitionUsage
- MultipleUsages
- HierarchicalReference
- Performance500Signals

### Implementation Steps

#### Step 1: Complete SymbolInfo Struct ✓ (Done)
```cpp
struct SymbolInfo {
  std::string symbol_name;
  std::string symbol_type;
  int definition_line, definition_column;
  std::vector<int> usage_lines, usage_columns;
  bool is_port, is_parameter;
  std::string port_direction;
  bool has_definition;
};
```

#### Step 2: Implement BuildSymbolTable (2-3 hours)

**Track Variable Declarations:**
```cpp
// Find kDataDeclaration nodes
auto var_decls = SearchSyntaxTree(root, NodekDataDeclaration());
for (each declaration) {
  - Extract symbol name
  - Calculate line/column from source_text offset
  - Store in symbol_table
}
```

**Track Port Declarations:**
```cpp
// Find kPortDeclaration nodes
// Extract: name, direction (input/output/inout), line/column
```

**Track Parameter Declarations:**
```cpp
// Find kParamDeclaration nodes
// Mark as parameter, extract name and location
```

#### Step 3: Track Reference Usage (1-2 hours)

**Find all kReference nodes:**
```cpp
auto references = SearchSyntaxTree(root, NodekReference());
for (each reference) {
  - Extract symbol name
  - Calculate line/column
  - Add to symbol_table[name].usage_lines/usage_columns
}
```

#### Step 4: Add AddCrossReferenceMetadata Function (1 hour)

```cpp
static void AddCrossReferenceMetadata(
    json &node_json,
    const verible::SyntaxTreeNode &node,
    const std::unordered_map<std::string, SymbolInfo>& symbol_table,
    std::string_view source_text,
    const std::string& current_symbol) {
  
  json cross_ref = json::object();
  cross_ref["symbol"] = current_symbol;
  
  auto it = symbol_table.find(current_symbol);
  if (it != symbol_table.end()) {
    const auto& info = it->second;
    
    // Determine if this is definition or usage based on location
    int current_line = CalculateLineNumber(node, source_text);
    
    if (current_line == info.definition_line) {
      cross_ref["ref_type"] = "definition";
    } else {
      cross_ref["ref_type"] = "usage";
    }
    
    cross_ref["definition_location"] = {
      {"line", info.definition_line},
      {"column", info.definition_column}
    };
    
    if (info.is_port) {
      cross_ref["port_direction"] = info.port_direction;
    }
    if (info.is_parameter) {
      cross_ref["is_parameter"] = true;
    }
  }
  
  if (!node_json.contains("metadata")) {
    node_json["metadata"] = json::object();
  }
  node_json["metadata"]["cross_ref"] = cross_ref;
}
```

#### Step 5: Integration (30 min)

Modify `VerilogTreeToJsonConverter`:
```cpp
// In ConvertVerilogTreeToJson():
auto symbol_table = BuildSymbolTable(*tree, source_text);

// Pass symbol_table to converter
VerilogTreeToJsonConverter converter(..., symbol_table);

// In Visit() for kDataDeclaration:
AddCrossReferenceMetadata(node_json, node, symbol_table_, source_text, symbol_name);

// In Visit() for kReference:
AddCrossReferenceMetadata(node_json, node, symbol_table_, source_text, symbol_name);
```

#### Step 6: Test & Debug (1-2 hours)

Run tests incrementally:
- Test 1: SimpleVariableDefinitionUsage
- Test 2: PortDefinitions
- Test 3: ParameterDefinitionUsage
- Test 4: MultipleUsages
- Test 5: HierarchicalReference
- Test 12: Performance500Signals

**Expected Result:** 12/12 tests passing

---

## Phase C: Scope/Hierarchy Metadata (Target: 14/14 tests)

### Test File Location
`verible/verilog/CST/verilog-tree-json-scope-hierarchy_test.cc`

### Expected Features

1. **Module Hierarchy Tracking**
   - Parent/child module relationships
   - Instance paths

2. **Scope Resolution**
   - Local scope vs module scope
   - Hierarchical name resolution

3. **Scope Metadata Structure**
```json
{
  "scope_info": {
    "scope_type": "module" | "function" | "block",
    "scope_name": "test_module",
    "parent_scope": "top_module",
    "hierarchy_path": "top.test_module",
    "local_symbols": ["clk", "rst", "data"]
  }
}
```

### Implementation Steps

#### Step 1: Add ScopeInfo Struct
```cpp
struct ScopeInfo {
  std::string scope_name;
  std::string scope_type;
  std::string parent_scope;
  std::string hierarchy_path;
  std::vector<std::string> local_symbols;
  int definition_line, definition_column;
};
```

#### Step 2: Build Scope Tree
```cpp
static std::map<std::string, ScopeInfo> BuildScopeTree(
    const verible::Symbol& root, 
    std::string_view source_text);
```

Track:
- Module declarations (kModuleDeclaration)
- Function/task declarations
- Begin/end blocks
- Generate blocks

#### Step 3: Add AddScopeMetadata Function
```cpp
static void AddScopeMetadata(
    json &node_json,
    const verible::SyntaxTreeNode &node,
    const std::map<std::string, ScopeInfo>& scope_tree,
    const std::string& current_scope);
```

#### Step 4: Integration & Testing
Similar pattern to Phase A & B

**Expected Result:** 14/14 tests passing

---

## Phase D: Dataflow Metadata (Target: 10/10 tests)

### Test File Location
`verible/verilog/CST/verilog-tree-json-dataflow_test.cc`

### Expected Features

1. **Driver Tracking**
   - What drives each signal
   - Assignment sources

2. **Load Tracking**
   - Where signals are used
   - Fan-out analysis

3. **Dataflow Metadata Structure**
```json
{
  "dataflow_info": {
    "signal": "data_out",
    "drivers": [
      {"type": "assignment", "line": 10, "source": "data_in & mask"}
    ],
    "loads": [
      {"type": "reference", "line": 15, "location": "always block"}
    ],
    "fanout": 3
  }
}
```

### Implementation Steps

#### Step 1: Add DataflowInfo Struct
```cpp
struct DataflowInfo {
  std::string signal_name;
  std::vector<std::string> drivers;
  std::vector<int> driver_lines;
  std::vector<std::string> loads;
  std::vector<int> load_lines;
  int fanout;
};
```

#### Step 2: Track Assignments
```cpp
static std::unordered_map<std::string, DataflowInfo> BuildDataflowTable(
    const verible::Symbol& root,
    std::string_view source_text);
```

Track:
- Continuous assignments (assign statements)
- Blocking assignments (=)
- Non-blocking assignments (<=)
- Port connections

#### Step 3: Add AddDataflowMetadata Function
```cpp
static void AddDataflowMetadata(
    json &node_json,
    const verible::SyntaxTreeNode &node,
    const std::unordered_map<std::string, DataflowInfo>& dataflow_table,
    const std::string& signal_name);
```

#### Step 4: Integration & Testing

**Expected Result:** 10/10 tests passing

---

## Deployment Plan

### Step 1: Build Verible Binary
```bash
cd /Users/jonguksong/Projects/verible
bazel build //verible/verilog/tools/syntax:verible-verilog-syntax --macos_minimum_os=10.15
```

### Step 2: Deploy to VeriPG
```bash
cp bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax \
   /path/to/veripg/bin/
```

### Step 3: Verify Functionality
```bash
cd /path/to/veripg
# Run VeriPG test suite with new Verible binary
# Verify 460x type resolution speedup
```

### Step 4: Create Release Documentation
- Update CHANGELOG
- Create release notes
- Document new metadata fields
- Create user guide for VeriPG team

### Step 5: Tag Release
```bash
git tag -a veripg-phases-b-c-d-v1.0 -m "Complete Phases B-D: Cross-ref, Scope, Dataflow"
git push origin veripg-phases-b-c-d-v1.0
```

---

## Time Estimates

| Phase | Estimated Time | Complexity |
|-------|---------------|------------|
| Phase B | 4-6 hours | Medium (symbol table, cross-ref) |
| Phase C | 3-5 hours | Medium-High (scope tree, hierarchy) |
| Phase D | 2-4 hours | Medium (dataflow tracking) |
| Deployment | 1-2 hours | Low (build, test, document) |
| **Total** | **10-17 hours** | **Full implementation** |

---

## Success Criteria

✅ Phase B: 12/12 tests passing  
✅ Phase C: 14/14 tests passing  
✅ Phase D: 10/10 tests passing  
✅ All phases integrated  
✅ Verible binary built successfully  
✅ Deployed to VeriPG  
✅ VeriPG tests passing with new binary  
✅ Performance improvement verified  
✅ Documentation complete  
✅ Release tagged

---

## Next Steps

1. **Immediate:** Complete Phase B implementation following steps above
2. **Then:** Move to Phase C
3. **Then:** Move to Phase D
4. **Finally:** Deploy and verify

## Files to Modify

- **Phase B:**
  - `verible/verilog/CST/verilog-tree-json.cc` (~500 lines)
  - Test file already exists

- **Phase C:**
  - Same file (~400 lines)
  - Test file exists

- **Phase D:**
  - Same file (~300 lines)
  - Test file exists

**Total Additional Code:** ~1200 lines across all phases

---

**Status:** Phase A Complete ✓, Phase B In Progress (6/12 tests passing)  
**Next Action:** Implement BuildSymbolTable function

