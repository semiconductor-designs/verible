# Phase 4 Implementation Plan: Behavioral Block Metadata

**Status:** PLANNING  
**Phase:** Phase 4 - Behavioral Semantics  
**Target:** `kAlwaysStatement` metadata for behavioral graph construction  
**Date:** October 10, 2024

---

## Executive Summary

**Goal:** Add `metadata` field to `kAlwaysStatement` CST nodes to enable clean extraction of behavioral semantics (combinational vs. sequential logic, clock/reset detection, assignment types).

**Approach:** Apply the proven Phase 3 pattern (expression metadata) to procedural blocks.

**Effort:** 3-5 days
- Day 1-2: Core implementation
- Day 3: Testing & validation
- Day 4-5: Edge cases & refinement

**Success Criteria:**
- ✅ 7 test cases passing (TDD)
- ✅ 100% backward compatible
- ✅ Reduces VeriPG code by ~95%

---

## Phase 3 Success Reference

**What worked well in Phase 3:**
1. ✅ **TDD methodology** - Write tests first, then implement
2. ✅ **Phased approach** - Binary → Ternary → Unary → Function calls
3. ✅ **Helper functions** - Modular, testable utilities
4. ✅ **CST traversal** - Use existing Verible utilities
5. ✅ **Metadata schema** - Clean, well-defined JSON structure
6. ✅ **Backward compatibility** - Additive-only changes

**Apply to Phase 4:** Same winning pattern!

---

## Implementation Strategy

### Phase 4A: Core Metadata (Days 1-2)

#### 1. Metadata Schema Definition
```cpp
struct AlwaysBlockMetadata {
  std::string block_type;        // "always_ff", "always_comb", etc.
  bool is_sequential;
  bool is_combinational;
  SensitivityInfo sensitivity;
  std::optional<ClockInfo> clock_info;
  std::optional<ResetInfo> reset_info;
  std::string assignment_type;   // "blocking", "nonblocking", "mixed"
};
```

#### 2. Core Helper Functions

**A. Block Type Detection**
```cpp
static std::string DetectBlockType(const SyntaxTreeNode &always_node) {
  // Check keyword token type
  // TK_always_ff → "always_ff"
  // TK_always_comb → "always_comb"
  // TK_always_latch → "always_latch"
  // TK_always → "always"
}
```

**B. Sequential Detection**
```cpp
static bool IsSequentialBlock(const SyntaxTreeNode &always_node) {
  // Get event control
  // Check for posedge/negedge in sensitivity list
  auto *timing_ctrl = GetProceduralTimingControlFromAlways(always_node);
  auto *event_ctrl = GetEventControlFromProceduralTimingControl(*timing_ctrl);
  // Traverse event list for edge keywords
}
```

**C. Sensitivity List Extraction**
```cpp
static json ExtractSensitivityList(const SyntaxTreeNode &always_node) {
  // Extract all signals from event control
  // Determine edge type for each: "posedge", "negedge", "level", or null
  // Return array of {name, edge} objects
}
```

**D. Clock Detection**
```cpp
static std::optional<ClockInfo> DetectClock(const json &sensitivity) {
  // First signal with posedge/negedge is typically the clock
  for (auto &sig : sensitivity["signals"]) {
    if (sig["edge"] == "posedge" || sig["edge"] == "negedge") {
      return ClockInfo{sig["name"], sig["edge"]};
    }
  }
}
```

**E. Reset Detection**
```cpp
static std::optional<ResetInfo> DetectReset(
    const json &sensitivity, 
    const SyntaxTreeNode &always_body) {
  // Method 1: Second edge signal in sensitivity (async reset)
  // Method 2: First if-condition in body (sync reset)
  // Determine active high/low from edge or condition
}
```

**F. Assignment Type Detection**
```cpp
static std::string DetectAssignmentType(const SyntaxTreeNode &always_body) {
  int blocking = 0;
  int nonblocking = 0;
  
  // Traverse body, count operators
  TraverseAssignments(always_body, [&](const Symbol &assign) {
    if (IsBlockingAssignment(assign)) blocking++;
    if (IsNonblockingAssignment(assign)) nonblocking++;
  });
  
  if (nonblocking > 0 && blocking == 0) return "nonblocking";
  if (blocking > 0 && nonblocking == 0) return "blocking";
  return "mixed";
}
```

#### 3. Main Metadata Generation

```cpp
static void AddAlwaysBlockMetadata(json &node_json,
                                    const SyntaxTreeNode &node) {
  json metadata = json::object();
  
  // 1. Block type
  metadata["block_type"] = DetectBlockType(node);
  
  // 2. Sensitivity list
  metadata["sensitivity"] = ExtractSensitivityList(node);
  
  // 3. Sequential/combinational flags
  metadata["is_sequential"] = IsSequentialBlock(node);
  metadata["is_combinational"] = !metadata["is_sequential"] || 
                                  metadata["block_type"] == "always_comb";
  
  // 4. Clock info (if sequential)
  if (metadata["is_sequential"]) {
    auto clock = DetectClock(metadata["sensitivity"]);
    if (clock) {
      metadata["clock_info"] = json{
        {"signal", clock->signal},
        {"edge", clock->edge}
      };
    }
  }
  
  // 5. Reset info (if present)
  auto reset = DetectReset(metadata["sensitivity"], node);
  if (reset) {
    metadata["reset_info"] = json{
      {"signal", reset->signal},
      {"type", reset->type},
      {"active", reset->active},
      {"edge", reset->edge}
    };
  }
  
  // 6. Assignment type
  metadata["assignment_type"] = DetectAssignmentType(node);
  
  node_json["metadata"] = metadata;
}
```

#### 4. Integration into Visit()

```cpp
void VerilogTreeToJsonConverter::Visit(const SyntaxTreeNode &node) {
  *value_ = json::object();
  (*value_)["tag"] = NodeEnumToString(static_cast<NodeEnum>(node.Tag().tag));
  
  // ... existing code ...
  
  // Add metadata for supported node types
  NodeEnum tag = static_cast<NodeEnum>(node.Tag().tag);
  if (tag == NodeEnum::kBinaryExpression) {
    AddBinaryExpressionMetadata(node, *value_);
  } else if (tag == NodeEnum::kConditionExpression) {
    AddTernaryExpressionMetadata(*value_, node);
  } else if (tag == NodeEnum::kUnaryPrefixExpression) {
    AddUnaryExpressionMetadata(*value_, node);
  } else if (tag == NodeEnum::kFunctionCall || tag == NodeEnum::kSystemTFCall) {
    AddFunctionCallMetadata(*value_, node);
  } else if (tag == NodeEnum::kAlwaysStatement) {  // NEW!
    AddAlwaysBlockMetadata(*value_, node);
  }
  
  // ... rest of code ...
}
```

---

### Phase 4B: Testing (Day 3)

#### Test Cases (TDD Red → Green)

**Test 1: Sequential with Async Reset**
```systemverilog
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) q_o <= 1'b0;
  else q_o <= d_i;
end
```
Expected:
```json
{
  "block_type": "always_ff",
  "is_sequential": true,
  "is_combinational": false,
  "sensitivity": {
    "type": "edge",
    "signals": [
      {"name": "clk_i", "edge": "posedge"},
      {"name": "rst_ni", "edge": "negedge"}
    ]
  },
  "clock_info": {"signal": "clk_i", "edge": "posedge"},
  "reset_info": {
    "signal": "rst_ni",
    "type": "async",
    "active": "low",
    "edge": "negedge"
  },
  "assignment_type": "nonblocking"
}
```

**Test 2: Combinational (always_comb)**
```systemverilog
always_comb begin
  sum = a + b;
end
```
Expected:
```json
{
  "block_type": "always_comb",
  "is_sequential": false,
  "is_combinational": true,
  "sensitivity": {"type": "implicit", "signals": []},
  "assignment_type": "blocking"
}
```

**Test 3: Explicit Sensitivity List**
```systemverilog
always @(a or b or sel) begin
  if (sel) out = a;
  else out = b;
end
```
Expected:
```json
{
  "block_type": "always",
  "is_sequential": false,
  "is_combinational": true,
  "sensitivity": {
    "type": "explicit",
    "signals": [
      {"name": "a", "edge": "level"},
      {"name": "b", "edge": "level"},
      {"name": "sel", "edge": "level"}
    ]
  },
  "assignment_type": "blocking"
}
```

**Test 4: Implicit Sensitivity (@*)**
```systemverilog
always @* begin
  result = x + y;
end
```
Expected:
```json
{
  "block_type": "always",
  "is_sequential": false,
  "is_combinational": true,
  "sensitivity": {"type": "implicit", "signals": []},
  "assignment_type": "blocking"
}
```

**Test 5: Synchronous Reset**
```systemverilog
always_ff @(posedge clk_i) begin
  if (rst_i) counter <= 8'd0;
  else counter <= counter + 1;
end
```
Expected:
```json
{
  "block_type": "always_ff",
  "is_sequential": true,
  "is_combinational": false,
  "sensitivity": {
    "type": "edge",
    "signals": [{"name": "clk_i", "edge": "posedge"}]
  },
  "clock_info": {"signal": "clk_i", "edge": "posedge"},
  "reset_info": {
    "signal": "rst_i",
    "type": "sync",
    "active": "high",
    "edge": null
  },
  "assignment_type": "nonblocking"
}
```

**Test 6: Latch (always_latch)**
```systemverilog
always_latch begin
  if (en) q = d;
end
```
Expected:
```json
{
  "block_type": "always_latch",
  "is_sequential": false,
  "is_combinational": false,
  "sensitivity": {"type": "implicit", "signals": []},
  "assignment_type": "blocking"
}
```

**Test 7: Mixed Assignments (Warning)**
```systemverilog
always_ff @(posedge clk) begin
  a = b;    // Blocking
  c <= d;   // Non-blocking (mixed - bad!)
end
```
Expected:
```json
{
  "block_type": "always_ff",
  "is_sequential": true,
  "is_combinational": false,
  "sensitivity": {
    "type": "edge",
    "signals": [{"name": "clk", "edge": "posedge"}]
  },
  "clock_info": {"signal": "clk", "edge": "posedge"},
  "assignment_type": "mixed"
}
```

#### Test File Structure
```cpp
// verible/verilog/CST/verilog-tree-json-behavioral_test.cc

TEST(VerilogTreeJsonBehavioralTest, SequentialWithAsyncReset) { ... }
TEST(VerilogTreeJsonBehavioralTest, Combinational) { ... }
TEST(VerilogTreeJsonBehavioralTest, ExplicitSensitivity) { ... }
TEST(VerilogTreeJsonBehavioralTest, ImplicitSensitivity) { ... }
TEST(VerilogTreeJsonBehavioralTest, SynchronousReset) { ... }
TEST(VerilogTreeJsonBehavioralTest, Latch) { ... }
TEST(VerilogTreeJsonBehavioralTest, MixedAssignments) { ... }
```

---

### Phase 4C: Refinement (Days 4-5)

#### Edge Cases to Handle

1. **Multiple clocks** (rare but possible)
   - Keep first posedge/negedge as primary clock
   - Add warning in metadata?

2. **Complex reset conditions**
   - Handle `!rst`, `~rst`, `rst`, `!rst_n`
   - Detect active high/low from logic

3. **Nested conditionals**
   - Reset detection in first if-statement
   - Handle elsif/else branches

4. **Empty sensitivity lists**
   - `always_comb` → implicit
   - `always_ff` without event control → error case

5. **Parameterized clocks**
   - `@(posedge CLK_TYPE ? clk_a : clk_b)` → extract signal name

---

## CST Structure Reference

### kAlwaysStatement Structure
```
kAlwaysStatement
├── [0] Keyword (TK_always_ff / TK_always_comb / TK_always / TK_always_latch)
├── [1] kProceduralTimingControlStatement (optional)
│   ├── [0] kEventControl
│   │   ├── '@'
│   │   ├── kParenGroup or '*'
│   │   │   ├── '('
│   │   │   ├── Event expressions (posedge clk, negedge rst, etc.)
│   │   │   └── ')'
│   └── [1] Statement block
└── [2] Statement (if no timing control)
```

### Event Control Parsing
```cpp
// Use existing utilities:
GetProceduralTimingControlFromAlways(always_node)
GetEventControlFromProceduralTimingControl(timing_ctrl)
```

---

## Dependencies & Files

### Files to Modify

1. **`verible/verilog/CST/verilog-tree-json.cc`**
   - Add `AddAlwaysBlockMetadata()` function
   - Add helper functions (DetectBlockType, etc.)
   - Integrate into `Visit()` method

2. **`verible/verilog/CST/verilog-tree-json.h`**
   - No changes needed (metadata is internal)

3. **`verible/verilog/CST/BUILD`**
   - Add `:statement` dependency if needed

4. **`verible/verilog/CST/verilog-tree-json-behavioral_test.cc`** (NEW)
   - Create new test file for behavioral metadata
   - 7 comprehensive test cases

### Dependencies Required

- `statement.h` - GetProceduralTimingControlFromAlways, etc.
- `verilog-nonterminals.h` - NodeEnum definitions
- `verilog_lexer.h` - Token types (TK_always_ff, etc.)
- Existing JSON utilities from Phase 3

---

## Risk Assessment

### Low Risk
- ✅ **Pattern proven** - Phase 3 success
- ✅ **CST utilities exist** - GetProceduralTimingControlFromAlways, etc.
- ✅ **Backward compatible** - Additive only
- ✅ **Clear requirements** - Well-defined in Phase 4 request

### Medium Risk
- ⚠️ **Reset detection complexity** - Sync vs. async heuristics
- ⚠️ **Edge case handling** - Multiple clocks, parameterized signals
- ⚠️ **Assignment traversal** - Need to recursively count operators

### Mitigation
- Start with simple cases (Tests 1-4)
- Add complexity incrementally (Tests 5-7)
- Use TDD to catch edge cases early
- Leverage existing Verible CST traversal utilities

---

## Success Metrics

### For Verible
- ✅ All 7 test cases pass
- ✅ No regressions in existing tests
- ✅ Clean, maintainable code
- ✅ Documented in changelog

### For VeriPG
- ✅ 95% code reduction (380 → 20 lines)
- ✅ Correct behavioral classification
- ✅ Clock/reset detection working
- ✅ Phase 4 integration successful

---

## Timeline

### Week 1: Implementation
- **Day 1:** Setup + Block type & sequential detection
- **Day 2:** Sensitivity list + Clock/reset detection
- **Day 3:** Assignment type + Tests 1-4
- **Day 4:** Tests 5-7 + Edge cases
- **Day 5:** Polish + Documentation

### Week 2: VeriPG Integration
- **Day 6-7:** VeriPG Phase 4 implementation
- **Day 8:** End-to-end testing
- **Day 9:** Documentation updates
- **Day 10:** Release

---

## Open Questions

1. **Q:** Should we detect multiple clocks?  
   **A:** Yes, but keep first as primary. Add to sensitivity list.

2. **Q:** How to handle reset in elsif?  
   **A:** Only detect in first if-statement for now.

3. **Q:** Support `always_latch` warning metadata?  
   **A:** Yes, add to metadata for VeriPG to flag.

4. **Q:** Parameterized clock names?  
   **A:** Extract as-is, let VeriPG resolve parameters.

---

## Next Steps

1. ✅ **Review this plan** with team
2. 📝 **Create task breakdown** (GitHub issues)
3. 🔴 **TDD: Write Test 1** (SequentialWithAsyncReset)
4. 🟢 **Implement to pass Test 1**
5. 🔄 **Repeat for Tests 2-7**
6. 🚀 **Deploy to VeriPG**

---

## References

- **Phase 3 Success:** `doc/RELEASE_NOTES_METADATA_ENHANCEMENT.md`
- **Phase 4 Request:** `doc/VERIBLE_PHASE4_ENHANCEMENT_REQUEST.md`
- **CST Utilities:** `verible/verilog/CST/statement.{h,cc}`
- **Matchers:** `verible/verilog/CST/verilog-matchers.h`
- **Token Types:** `verible/verilog/parser/verilog_token_enum.h`

---

**Status:** ✅ Plan complete, ready for implementation  
**Confidence:** HIGH (Phase 3 pattern proven)  
**Estimated Completion:** 3-5 days  
**Expected Outcome:** 95% VeriPG code reduction, clean behavioral semantics

---

*"Phase 3 proved the pattern. Phase 4 applies it to behavioral blocks."*

**Let's build it!** 🚀

