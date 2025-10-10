# Verible Enhancement Request: Phase 4 Behavioral Graph Support

**Document Version:** 1.0  
**Date:** October 10, 2025  
**Priority:** HIGH (Next Phase)  
**Requester:** VeriPG Team  
**Target:** Verible Parser Enhancement  
**Impact:** Behavioral Semantics, Timing Analysis, RTL Synthesis

---

## Executive Summary

**Request:** Enhance Verible's JSON CST output with behavioral metadata for `always` blocks to enable clean extraction of behavioral semantics (combinational vs. sequential logic, clock/reset detection, assignment types).

**Benefit:** Enables VeriPG to construct accurate behavioral graphs without complex procedural block analysis, supporting correct RTL regeneration and timing analysis.

**Effort:** Medium (~3-5 days) - Similar pattern to Phase 3 expression metadata, but for procedural blocks.

**ROI:** High - Reduces VeriPG code by ~60%, enables critical behavioral analysis features.

---

## Problem Statement

### Current Challenge

SystemVerilog `always` blocks encode critical behavioral information:
- **Combinational vs. Sequential logic**
- **Clock edges** (posedge/negedge)
- **Reset signals** (sync/async)
- **Assignment types** (blocking `=` vs. non-blocking `<=`)
- **Sensitivity lists** (implicit `@*` vs. explicit)

**Without enhancement**, VeriPG must:
1. Parse `kAlwaysStatement` CST nodes
2. Traverse `kEventControl` to find clock/reset
3. Detect edge types (posedge/negedge)
4. Analyze sensitivity lists
5. Classify assignment types in procedural blocks
6. Infer combinational vs. sequential behavior

**Estimated code:** ~400-600 lines of complex, fragile parsing.

### What We Need

Add `metadata` field to `kAlwaysStatement` (and similar procedural block) nodes in Verible's JSON CST output.

**Example:**
```json
{
  "tag": "kAlwaysStatement",
  "metadata": {
    "block_type": "always_ff",
    "is_sequential": true,
    "sensitivity": {
      "type": "explicit",
      "signals": [
        {"name": "clk_i", "edge": "posedge"},
        {"name": "rst_ni", "edge": "negedge"}
      ]
    },
    "reset_info": {
      "signal": "rst_ni",
      "type": "async",
      "active": "low"
    },
    "assignment_type": "nonblocking"
  },
  "children": [...]
}
```

---

## Detailed Requirements

### 1. Always Block Metadata

#### Schema
```json
{
  "block_type": "always_ff" | "always_comb" | "always_latch" | "always",
  "is_sequential": boolean,
  "is_combinational": boolean,
  "sensitivity": {
    "type": "explicit" | "implicit" | "edge",
    "signals": [
      {
        "name": string,          // Signal name (e.g., "clk_i")
        "edge": "posedge" | "negedge" | "level" | null
      }
    ]
  },
  "clock_info": {               // Only if is_sequential == true
    "signal": string,           // Clock signal name
    "edge": "posedge" | "negedge"
  },
  "reset_info": {               // Optional
    "signal": string,           // Reset signal name
    "type": "sync" | "async",
    "active": "high" | "low",
    "edge": "posedge" | "negedge" | null
  },
  "assignment_type": "blocking" | "nonblocking" | "mixed"
}
```

#### Field Descriptions

**`block_type`** (string, required)
- Values: `"always_ff"`, `"always_comb"`, `"always_latch"`, `"always"`
- Directly from SystemVerilog keyword
- Example: `always_ff` → `"always_ff"`

**`is_sequential`** (boolean, required)
- `true` if block has edge-sensitive event control (posedge/negedge)
- `false` for combinational/latch logic
- Example: `always_ff @(posedge clk)` → `true`

**`is_combinational`** (boolean, required)
- `true` if block is combinational (always_comb, always @*)
- `false` for sequential/latch logic
- Example: `always_comb` → `true`

**`sensitivity.type`** (string, required)
- `"explicit"`: Has explicit sensitivity list with edges
- `"implicit"`: Uses `@*` or `always_comb`
- `"edge"`: Edge-triggered (posedge/negedge)
- Example: `@*` → `"implicit"`, `@(posedge clk)` → `"edge"`

**`sensitivity.signals`** (array, required)
- List of signals in sensitivity list
- Each signal has `name` and `edge` type
- Example: `@(posedge clk or negedge rst_n)` → `[{name: "clk", edge: "posedge"}, {name: "rst_n", edge: "negedge"}]`

**`clock_info`** (object, optional)
- Only present if `is_sequential == true`
- Identifies the primary clock signal
- Example: `@(posedge clk_i)` → `{signal: "clk_i", edge: "posedge"}`

**`reset_info`** (object, optional)
- Only present if reset signal detected
- Distinguishes sync vs. async reset
- Identifies active high/low
- Example: `@(posedge clk or negedge rst_n)` → `{signal: "rst_n", type: "async", active: "low", edge: "negedge"}`

**`assignment_type`** (string, required)
- `"blocking"`: Uses `=` assignments only
- `"nonblocking"`: Uses `<=` assignments only
- `"mixed"`: Uses both (warning case!)
- Example: `q <= d;` → `"nonblocking"`

---

## Examples

### Example 1: Sequential Logic (Flip-Flop)

**SystemVerilog:**
```systemverilog
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) begin
    q_o <= 1'b0;
  end else begin
    q_o <= d_i;
  end
end
```

**Enhanced JSON:**
```json
{
  "tag": "kAlwaysStatement",
  "metadata": {
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
    "clock_info": {
      "signal": "clk_i",
      "edge": "posedge"
    },
    "reset_info": {
      "signal": "rst_ni",
      "type": "async",
      "active": "low",
      "edge": "negedge"
    },
    "assignment_type": "nonblocking"
  },
  "children": [...]
}
```

**VeriPG Usage:**
```python
# Clean extraction!
meta = always_node['metadata']
if meta['is_sequential']:
    clk = meta['clock_info']['signal']
    edge = meta['clock_info']['edge']
    # Create clocked_by edge: BehavioralBlock --clocked_by--> Port(clk)
```

---

### Example 2: Combinational Logic

**SystemVerilog:**
```systemverilog
always_comb begin
  sum = a + b;
  carry = (a & b) | (a & cin) | (b & cin);
end
```

**Enhanced JSON:**
```json
{
  "tag": "kAlwaysStatement",
  "metadata": {
    "block_type": "always_comb",
    "is_sequential": false,
    "is_combinational": true,
    "sensitivity": {
      "type": "implicit",
      "signals": []
    },
    "assignment_type": "blocking"
  },
  "children": [...]
}
```

**VeriPG Usage:**
```python
meta = always_node['metadata']
if meta['is_combinational']:
    assert meta['assignment_type'] == 'blocking', "Combinational should use blocking"
    # Create BehavioralBlock with is_sequential=false
```

---

### Example 3: Explicit Sensitivity List

**SystemVerilog:**
```systemverilog
always @(a or b or sel) begin
  if (sel)
    out = a;
  else
    out = b;
end
```

**Enhanced JSON:**
```json
{
  "tag": "kAlwaysStatement",
  "metadata": {
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
  },
  "children": [...]
}
```

**VeriPG Usage:**
```python
# Extract sensitive_to edges
for sig in meta['sensitivity']['signals']:
    # Create edge: BehavioralBlock --sensitive_to--> Variable(sig['name'])
```

---

### Example 4: Synchronous Reset

**SystemVerilog:**
```systemverilog
always_ff @(posedge clk_i) begin
  if (rst_i) begin
    counter <= 8'd0;
  end else begin
    counter <= counter + 1;
  end
end
```

**Enhanced JSON:**
```json
{
  "tag": "kAlwaysStatement",
  "metadata": {
    "block_type": "always_ff",
    "is_sequential": true,
    "is_combinational": false,
    "sensitivity": {
      "type": "edge",
      "signals": [
        {"name": "clk_i", "edge": "posedge"}
      ]
    },
    "clock_info": {
      "signal": "clk_i",
      "edge": "posedge"
    },
    "reset_info": {
      "signal": "rst_i",
      "type": "sync",
      "active": "high",
      "edge": null
    },
    "assignment_type": "nonblocking"
  },
  "children": [...]
}
```

**VeriPG Usage:**
```python
reset = meta['reset_info']
if reset['type'] == 'sync':
    # Synchronous reset: only in sensitivity if async
    # Create reset_by edge with sync metadata
```

---

## Implementation Guidance

### Where to Add Metadata

**Primary Target:** `kAlwaysStatement` CST node

**Related Targets (Future):**
- `kInitialStatement` (for testbenches)
- `kFinalStatement` (for cleanup)

### Detection Logic

#### 1. Block Type Detection
```cpp
// Straightforward keyword detection
if (keyword == "always_ff") return "always_ff";
if (keyword == "always_comb") return "always_comb";
if (keyword == "always_latch") return "always_latch";
return "always";
```

#### 2. Sequential vs. Combinational
```cpp
// Check event control for edges
bool is_sequential = false;
for (auto& event : event_control) {
    if (event.type == POSEDGE || event.type == NEGEDGE) {
        is_sequential = true;
        break;
    }
}

bool is_combinational = (keyword == "always_comb") || 
                       (sensitivity == "@*") || 
                       (!is_sequential);
```

#### 3. Clock Detection
```cpp
// First posedge/negedge signal is usually clock
for (auto& signal : sensitivity_list) {
    if (signal.edge == POSEDGE || signal.edge == NEGEDGE) {
        clock_info = {signal.name, signal.edge};
        break;
    }
}
```

#### 4. Reset Detection
```cpp
// Second edge signal (if any) is usually async reset
// Or: look for reset in first if-statement condition
if (sensitivity_list.size() > 1) {
    auto& second = sensitivity_list[1];
    if (second.edge == POSEDGE || second.edge == NEGEDGE) {
        reset_info = {
            .signal = second.name,
            .type = "async",
            .active = (second.edge == NEGEDGE) ? "low" : "high",
            .edge = second.edge
        };
    }
}

// For sync reset, parse first if-statement
// (More complex - can be heuristic-based)
```

#### 5. Assignment Type Detection
```cpp
// Traverse procedural block, count assignment operators
int blocking_count = 0;
int nonblocking_count = 0;

traverse_assignments(always_body, [&](auto& assign) {
    if (assign.operator == "=") blocking_count++;
    if (assign.operator == "<=") nonblocking_count++;
});

string assignment_type;
if (blocking_count > 0 && nonblocking_count == 0) 
    assignment_type = "blocking";
else if (nonblocking_count > 0 && blocking_count == 0)
    assignment_type = "nonblocking";
else
    assignment_type = "mixed";  // Warning!
```

---

## Testing Requirements

### Test Cases

#### 1. Basic Sequential (FF with async reset)
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) q <= 0;
  else q <= d;
end
```
Expected: `is_sequential=true`, `clock_info`, `reset_info.type=async`

#### 2. Combinational (always_comb)
```systemverilog
always_comb begin
  y = a & b;
end
```
Expected: `is_combinational=true`, `assignment_type=blocking`

#### 3. Explicit Sensitivity
```systemverilog
always @(a or b) begin
  out = a ^ b;
end
```
Expected: `sensitivity.type=explicit`, `sensitivity.signals` contains a, b

#### 4. Implicit Sensitivity
```systemverilog
always @* begin
  result = x + y;
end
```
Expected: `sensitivity.type=implicit`

#### 5. Synchronous Reset
```systemverilog
always_ff @(posedge clk) begin
  if (rst) counter <= 0;
  else counter <= counter + 1;
end
```
Expected: `reset_info.type=sync`, `reset_info.signal=rst`

#### 6. Latch (Warning Case)
```systemverilog
always_latch begin
  if (en) q = d;
end
```
Expected: `block_type=always_latch`, warning metadata

#### 7. Mixed Assignments (Error Case)
```systemverilog
always_ff @(posedge clk) begin
  a = b;    // Blocking
  c <= d;   // Non-blocking (mixed - bad!)
end
```
Expected: `assignment_type=mixed`

---

## Backward Compatibility

### Strategy: Additive Only

✅ **Safe:** Add `metadata` field to existing nodes  
✅ **Safe:** Existing tools ignore unknown fields  
✅ **Safe:** VeriPG checks for `metadata` existence before using  

### VeriPG Fallback
```python
if 'metadata' in always_node:
    # Use enhanced metadata (Phase 4+)
    meta = always_node['metadata']
    is_sequential = meta['is_sequential']
else:
    # Fallback: manual parsing (Phase 3 approach)
    is_sequential = self._detect_sequential_manual(always_node)
```

### Versioning
- Verible version tag in JSON: `"verible_version": "0.0-xxxx"`
- VeriPG can check version and adapt

---

## Benefits for VeriPG

### Code Reduction
| Task | Without Enhancement | With Enhancement | Reduction |
|------|---------------------|------------------|-----------|
| Block type detection | ~50 lines | 1 line | 98% |
| Clock/reset extraction | ~150 lines | 5 lines | 97% |
| Sensitivity analysis | ~100 lines | 10 lines | 90% |
| Assignment type check | ~80 lines | 1 line | 99% |
| **Total** | **~380 lines** | **~20 lines** | **~95%** |

### Reliability
- ✅ No fragile heuristics
- ✅ Correct edge detection
- ✅ Proper async vs. sync reset distinction
- ✅ Consistent with Verible's internal parsing

### Enables Critical Features
1. **Timing Analysis:** Clock domain identification
2. **RTL Synthesis:** Blocking vs. non-blocking verification
3. **Verification:** Reset behavior validation
4. **Optimization:** Combinational path analysis
5. **Documentation:** Auto-generate timing diagrams

---

## Comparison: Phase 3 vs. Phase 4

| Aspect | Phase 3 (Expressions) | Phase 4 (Behavioral) |
|--------|----------------------|---------------------|
| **Complexity** | Medium | Medium |
| **CST Nodes** | `kBinaryExpression`, `kConditionExpression` | `kAlwaysStatement` |
| **Metadata Fields** | `operation`, `operator`, `operands` | `block_type`, `sensitivity`, `clock_info` |
| **Code Reduction** | 80% | 95% |
| **Implementation Effort** | 2-3 days | 3-5 days |
| **Testing Complexity** | Low | Medium |

**Similar pattern, proven success!**

---

## Success Criteria

### For Verible Team
- ✅ `metadata` field added to `kAlwaysStatement` nodes
- ✅ All 7 test cases pass
- ✅ Backward compatible (existing tools unaffected)
- ✅ Documented in Verible changelog

### For VeriPG Team
- ✅ Clean extraction (~20 lines vs. 380)
- ✅ Correct behavioral classification
- ✅ Clock/reset detection working
- ✅ All Phase 4 tests passing

---

## Timeline & Priority

### Proposed Schedule
- **Week 1:** Implementation (3-5 days)
- **Week 2:** Testing & validation
- **Week 3:** VeriPG integration (Phase 4)

### Priority Justification
**HIGH** because:
1. Phase 4 is next in VeriPG roadmap
2. Behavioral semantics are critical for RTL analysis
3. Proven pattern from Phase 3 success
4. Blocks VeriPG progress without it

---

## Alternative: Without Enhancement

If enhancement is not feasible, VeriPG can:
1. Implement ~380 lines of manual parsing
2. Accept ~95% accuracy (heuristics)
3. Slower development (3-4 weeks vs. 1 week)
4. Higher maintenance burden

**Recommendation:** Implement enhancement for long-term quality.

---

## Contact & Questions

**VeriPG Team Lead:** [Your Name]  
**Questions:** Please create GitHub issue in VeriPG repo  
**Reference:** This document + Phase 3 success story

---

## Appendix: Complete Metadata Schema

```typescript
interface AlwaysBlockMetadata {
  block_type: "always_ff" | "always_comb" | "always_latch" | "always";
  is_sequential: boolean;
  is_combinational: boolean;
  
  sensitivity: {
    type: "explicit" | "implicit" | "edge";
    signals: Array<{
      name: string;
      edge: "posedge" | "negedge" | "level" | null;
    }>;
  };
  
  clock_info?: {
    signal: string;
    edge: "posedge" | "negedge";
  };
  
  reset_info?: {
    signal: string;
    type: "sync" | "async";
    active: "high" | "low";
    edge: "posedge" | "negedge" | null;
  };
  
  assignment_type: "blocking" | "nonblocking" | "mixed";
}
```

---

## Summary

**What:** Add behavioral metadata to `kAlwaysStatement` nodes  
**Why:** Enable clean behavioral graph construction in VeriPG  
**How:** Similar pattern to Phase 3 expression metadata (proven success!)  
**Effort:** 3-5 days implementation  
**Impact:** 95% code reduction, critical for Phase 4  

**Phase 3 Success:** Enhanced Verible delivered 80% code reduction, same-day turnaround!  
**Phase 4 Request:** Apply same winning pattern to behavioral blocks.

---

*"Enhanced Verible + VeriPG = Powerful Semantic Graphs"*

**Let's make Phase 4 as successful as Phase 3!** 🚀

