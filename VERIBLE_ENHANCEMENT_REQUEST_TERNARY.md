# Verible Enhancement Request: Ternary Expression Metadata

**Request ID:** VeriPG-2025-001  
**Requesting Project:** VeriPG (SystemVerilog Parser for Graph Construction)  
**Priority:** Medium  
**Date:** October 16, 2025  
**VeriPG Version:** v4.5.0

## Executive Summary

VeriPG requires enhanced metadata for ternary conditional expressions (`? :`) to enable:
- **Multiplexer (mux) detection** for clock domain crossing (CDC) analysis
- **Signal source tracking** through conditional assignments
- **Data flow analysis** with conditional paths

Currently, Verible parses ternary expressions but doesn't provide structured metadata to identify the three components (condition, true_expr, false_expr) in a way that enables graph construction.

## Use Case: CDC Analysis

### Real-World Example

```systemverilog
// Clock domain crossing hazard
wire clk_selected;
assign clk_selected = sel ? clk_main : clk_io;  // Mux between different clock domains!

reg [7:0] data_out;
always_ff @(posedge clk_selected) begin  // DANGEROUS: clock source depends on sel
    data_out <= data_in;
end
```

**What VeriPG needs to detect:**
1. `clk_selected` is driven by a ternary expression (mux)
2. The two source signals (`clk_main`, `clk_io`) come from different clock domains
3. This creates a **CDC hazard** (clock domain crossing violation)

**Current limitation:** Without structured ternary metadata, VeriPG cannot:
- Distinguish muxes from other multi-driver scenarios
- Trace signal sources through conditional assignments
- Identify CDC hazards involving clock muxes

## Current Verible CST Structure

### What We Currently See

When parsing: `assign out = sel ? a : b;`

Verible currently produces a CST like:
```json
{
  "tag": "kNetVariableAssignment",
  "children": [
    {"tag": "kUnqualifiedId", "text": "out"},
    {"tag": "="},
    {
      "tag": "kExpression",
      "children": [
        {"tag": "kUnqualifiedId", "text": "sel"},
        {"tag": "?"},
        {"tag": "kUnqualifiedId", "text": "a"},
        {"tag": ":"},
        {"tag": "kUnqualifiedId", "text": "b"}
      ]
    }
  ]
}
```

**Problem:** The ternary components are flat children of `kExpression`. We cannot reliably identify:
- Which part is the condition (`sel`)
- Which part is the true branch (`a`)
- Which part is the false branch (`b`)

Without `?` and `:` as reliable markers, parsing becomes fragile and error-prone.

## Requested Enhancement

### Option 1: Dedicated Ternary Node (Preferred)

Add a dedicated `kTernaryExpression` or `kConditionalExpression` node type with structured children:

```json
{
  "tag": "kNetVariableAssignment",
  "children": [
    {"tag": "kUnqualifiedId", "text": "out"},
    {"tag": "="},
    {
      "tag": "kTernaryExpression",  // NEW: Dedicated node type
      "children": [
        {
          "tag": "kCondition",       // NEW: Explicit condition field
          "children": [
            {"tag": "kUnqualifiedId", "text": "sel"}
          ]
        },
        {
          "tag": "kTrueExpression",  // NEW: Explicit true branch
          "children": [
            {"tag": "kUnqualifiedId", "text": "a"}
          ]
        },
        {
          "tag": "kFalseExpression", // NEW: Explicit false branch
          "children": [
            {"tag": "kUnqualifiedId", "text": "b"}
          ]
        }
      ]
    }
  ]
}
```

**Benefits:**
- ✅ Unambiguous identification of ternary expressions
- ✅ Clear separation of condition, true, and false branches
- ✅ Consistent with other structured nodes (e.g., `kIfClause`, `kCaseItem`)
- ✅ Enables reliable graph construction

### Option 2: Enhanced Metadata (Alternative)

If changing CST structure is too disruptive, add metadata fields:

```json
{
  "tag": "kExpression",
  "metadata": {
    "expression_type": "ternary",      // NEW: Identify as ternary
    "condition": "sel",                 // NEW: Condition text
    "true_branch": "a",                 // NEW: True branch text
    "false_branch": "b"                 // NEW: False branch text
  },
  "children": [...]
}
```

**Benefits:**
- ✅ Non-breaking (CST structure unchanged)
- ✅ Provides necessary information
- ⚠️ Less structured than Option 1

## Scope of Request

### What VeriPG Needs to Extract

For ternary expressions in these contexts:

1. **Continuous Assignments**
   ```systemverilog
   assign out = sel ? a : b;
   ```

2. **Procedural Assignments**
   ```systemverilog
   always_comb begin
       out = sel ? a : b;
   end
   ```

3. **Port Connections**
   ```systemverilog
   child u_child(.data(sel ? data_a : data_b));
   ```

4. **Nested Ternaries**
   ```systemverilog
   assign out = sel1 ? (sel2 ? a : b) : (sel3 ? c : d);
   ```

5. **Right-Hand Side Expressions**
   ```systemverilog
   assign result = (sel ? a : b) + offset;
   ```

### Information Required Per Ternary

For each ternary expression, VeriPG needs:

| Field | Type | Description | Example |
|-------|------|-------------|---------|
| **condition** | Expression | Selector/condition | `sel` |
| **true_branch** | Expression | Value when condition is true | `a` |
| **false_branch** | Expression | Value when condition is false | `b` |
| **result_target** | Identifier | What's being assigned (if any) | `out` |
| **location** | Position | Line/column info | Line 42, col 15 |

## Test Cases

### Test Case 1: Simple Ternary
```systemverilog
assign mux_out = sel ? data_a : data_b;
```

**Expected Output:**
- Ternary node detected
- Condition: `sel`
- True branch: `data_a`
- False branch: `data_b`

### Test Case 2: Nested Ternary
```systemverilog
assign out = sel1 ? (sel2 ? a : b) : c;
```

**Expected Output:**
- Outer ternary: condition=`sel1`, true=(nested ternary), false=`c`
- Inner ternary: condition=`sel2`, true=`a`, false=`b`

### Test Case 3: Ternary in Expression
```systemverilog
assign result = (enable ? data : 8'h00) + offset;
```

**Expected Output:**
- Ternary: condition=`enable`, true=`data`, false=`8'h00`
- Parent: binary addition with `offset`

### Test Case 4: Clock Mux (CDC Hazard)
```systemverilog
wire clk_mux;
assign clk_mux = clk_sel ? clk_main : clk_io;
```

**Expected Output:**
- Ternary on clock signal
- VeriPG will detect: `clk_mux` driven from multiple clock domains

### Test Case 5: Multi-Bit Mux
```systemverilog
assign data_out[7:0] = mode ? data_a[7:0] : data_b[7:0];
```

**Expected Output:**
- Ternary with bit-select on all parts
- Should preserve bit-selection information

## Integration with VeriPG

### How VeriPG Will Use This

Once Verible provides structured ternary metadata, VeriPG will:

1. **Build Ternary Expression Nodes**
   ```python
   ternary_node = VeriPGNodeV2(
       id="top.mux_out",
       node_type=NodeType.TERNARY_EXPRESSION,
       properties={
           "condition": "sel",
           "true_expr": "data_a",
           "false_expr": "data_b"
       }
   )
   ```

2. **Create Graph Edges**
   ```python
   # Condition edge
   VeriPGEdgeV2(source="sel", target="mux_out", edge_type=EdgeType.HAS_CONDITION)
   
   # Data path edges
   VeriPGEdgeV2(source="data_a", target="mux_out", edge_type=EdgeType.HAS_TRUE_EXPR)
   VeriPGEdgeV2(source="data_b", target="mux_out", edge_type=EdgeType.HAS_FALSE_EXPR)
   ```

3. **Enable Source Tracking**
   - Mark `mux_out` as `source_type = "MUX"`
   - Check if `data_a` and `data_b` have different `clock_source`
   - Flag CDC hazard if clocks differ

4. **MTBF Calculation**
   - Identify synchronizer chains
   - Calculate Mean Time Between Failures
   - Assess CDC violation severity

### VeriPG Schema (For Reference)

```python
# Node type already exists
NodeType.TERNARY_EXPRESSION = "TernaryExpression"

# Edge types to be added (pending this request)
EdgeType.HAS_CONDITION = "has_condition"
EdgeType.HAS_TRUE_EXPR = "has_true_expr"
EdgeType.HAS_FALSE_EXPR = "has_false_expr"
```

## Implementation Priority

### High Priority
- ✅ Simple ternary in continuous assignments
- ✅ Ternary in always_comb blocks
- ✅ Clear condition/true/false identification

### Medium Priority
- 🔄 Nested ternaries
- 🔄 Ternary in port connections
- 🔄 Ternary as part of larger expressions

### Low Priority
- ⏳ Complex nested ternaries (3+ levels)
- ⏳ Ternary in generate blocks
- ⏳ Ternary in function returns

## Validation

### How to Verify Implementation

VeriPG will validate by running:
```bash
cd VeriPG
python3 tests/test_source_tracker.py
```

**Success criteria:**
- 4 currently skipped tests should pass:
  - `test_mux_marked_as_multi_source`
  - `test_clock_mux_detected_as_cdc_hazard`
  - `test_mux_not_flagged_as_multi_driver`
  - `test_loop_detection_max_iterations` (partial)

**Test files:**
- `tests/fixtures/source_tracking/clock_mux.sv`
- `tests/fixtures/source_tracking/multi_driver.sv`

## Alternative Workarounds

If this enhancement is not feasible, VeriPG can work around it by:

1. **Pattern Matching on Operators**
   - Search for `?` and `:` operators in expression
   - Use heuristics to identify branches
   - ⚠️ Fragile and error-prone

2. **Text-Based Parsing**
   - Fall back to regex on source text
   - ⚠️ Defeats purpose of using Verible CST

3. **Partial Implementation**
   - Only support simple ternaries (no nesting)
   - ⚠️ Misses complex CDC hazards

**None of these are ideal.** Structured metadata from Verible would be far superior.

## References

### IEEE 1800-2017 Standard
- **Section 11.4.11:** Conditional operator (`?:`)
- **Syntax:** `cond_predicate ? expression1 : expression2`

### Similar Implementations
- **Slang Parser:** Provides `ConditionalExpression` node type
- **sv-parser (Rust):** Has `ConditionalExpression` with explicit fields
- **tree-sitter-verilog:** Uses `ternary_expression` with condition/consequence/alternative

### VeriPG Context
- **Project:** https://github.com/semiconductor-designs/VeriPG
- **Version:** v4.5.0 (Phase 0: Universal Source Tracking complete)
- **Next Phase:** Phase 1 (SDC Parser) then Phase 2 (CDC Analysis with MTBF)
- **Impact:** Ternary support blocks 4/44 source tracking tests

## Contact

**Project Maintainer:** VeriPG Team  
**GitHub:** https://github.com/semiconductor-designs/VeriPG  
**Documentation:** `docs/SOURCE_TRACKING.md`

**For questions about this request:**
- Open issue on VeriPG GitHub
- Reference: "VERIBLE_ENHANCEMENT_REQUEST_TERNARY.md"

---

## Appendix: Example VeriPG Usage

### Before (Without Ternary Support)
```python
# VeriPG cannot detect this mux
assign clk_mux = sel ? clk_a : clk_b;

# Result: clk_mux.source_type = unknown (first driver encountered)
# Missing: CDC hazard detection
```

### After (With Ternary Support)
```python
# VeriPG detects mux and CDC hazard
assign clk_mux = sel ? clk_a : clk_b;

# Result:
#   clk_mux.source_type = "MUX"
#   clk_mux.clock_source = None (ambiguous - two sources)
#   Warning: "Clock domain mux detected: sources from {clk_a: CLOCK_main, clk_b: CLOCK_io}"
```

**Impact:** Enables detection of critical CDC bugs that cause real silicon failures.

---

**Thank you for considering this enhancement!**

