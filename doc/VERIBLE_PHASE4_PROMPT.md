# Verible Phase 4 Enhancement Prompt

**To:** Verible Owner  
**From:** VeriPG Team  
**Subject:** Phase 4 Enhancement Request - Behavioral Block Metadata  
**Priority:** HIGH (Next Phase)

---

## Quick Context

**Phase 3 Success:** Your expression metadata enhancement was AMAZING! 
- ✅ Delivered same day
- ✅ Reduced VeriPG code by 80% (280 lines vs 500+)
- ✅ 10x more reliable
- ✅ Clean, maintainable solution

**Phase 4 Goal:** Apply the same winning pattern to `always` blocks for behavioral graph construction.

---

## What We Need

Add `metadata` field to `kAlwaysStatement` nodes for behavioral semantics.

### Core Metadata Schema

```json
{
  "tag": "kAlwaysStatement",
  "metadata": {
    "block_type": "always_ff" | "always_comb" | "always_latch" | "always",
    "is_sequential": boolean,
    "is_combinational": boolean,
    "sensitivity": {
      "type": "explicit" | "implicit" | "edge",
      "signals": [
        {"name": string, "edge": "posedge" | "negedge" | "level" | null}
      ]
    },
    "clock_info": {              // Only if is_sequential
      "signal": string,
      "edge": "posedge" | "negedge"
    },
    "reset_info": {              // Optional
      "signal": string,
      "type": "sync" | "async",
      "active": "high" | "low"
    },
    "assignment_type": "blocking" | "nonblocking" | "mixed"
  }
}
```

---

## Example 1: Sequential Logic (Most Common)

**Input:**
```systemverilog
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (!rst_ni) q_o <= 1'b0;
  else q_o <= d_i;
end
```

**Output:**
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
      "active": "low"
    },
    "assignment_type": "nonblocking"
  }
}
```

---

## Example 2: Combinational Logic

**Input:**
```systemverilog
always_comb begin
  sum = a + b;
end
```

**Output:**
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
  }
}
```

---

## Why This Matters

### Without Enhancement (Current State)
VeriPG must implement ~380 lines of complex parsing:
- Traverse event control to find clock/reset
- Detect posedge/negedge
- Analyze sensitivity lists
- Distinguish sync vs. async reset
- Check assignment operators throughout block

### With Enhancement (Requested)
VeriPG implements ~20 lines:
```python
meta = always_node['metadata']
if meta['is_sequential']:
    clk = meta['clock_info']['signal']
    # Create clocked_by edge
```

**Result:** 95% code reduction, same as Phase 3 success!

---

## Implementation Hints

### Detection Logic (Pseudo-code)

```python
# 1. Block type: straightforward
block_type = keyword  # "always_ff", "always_comb", etc.

# 2. Sequential detection
is_sequential = any(sig.edge in ['posedge', 'negedge'] 
                   for sig in sensitivity_list)

# 3. Clock detection (first edge signal)
for sig in sensitivity_list:
    if sig.edge in ['posedge', 'negedge']:
        clock_info = {'signal': sig.name, 'edge': sig.edge}
        break

# 4. Reset detection (second edge signal = async reset)
if len(edge_signals) > 1:
    reset_sig = edge_signals[1]
    reset_info = {
        'signal': reset_sig.name,
        'type': 'async',
        'active': 'low' if reset_sig.edge == 'negedge' else 'high'
    }

# 5. Assignment type (traverse procedural assignments)
blocking_count = count_assignments(block, operator='=')
nonblocking_count = count_assignments(block, operator='<=')
if nonblocking_count > 0 and blocking_count == 0:
    assignment_type = 'nonblocking'
elif blocking_count > 0 and nonblocking_count == 0:
    assignment_type = 'blocking'
else:
    assignment_type = 'mixed'  # Warning case!
```

---

## Test Cases (7 Required)

1. ✅ **Sequential with async reset:** `always_ff @(posedge clk or negedge rst_n)`
2. ✅ **Combinational:** `always_comb`
3. ✅ **Explicit sensitivity:** `always @(a or b)`
4. ✅ **Implicit sensitivity:** `always @*`
5. ✅ **Synchronous reset:** `always_ff @(posedge clk) if (rst)`
6. ✅ **Latch:** `always_latch`
7. ✅ **Mixed assignments:** `always_ff` with both `=` and `<=` (error)

---

## Timeline

**Estimated Effort:** 3-5 days (similar to Phase 3)
- Day 1-2: Implementation
- Day 3: Testing
- Day 4-5: Polish & validation

**VeriPG Integration:** 1 week after delivery (Phase 4 implementation)

---

## Deliverables

1. ✅ Enhanced Verible with `metadata` on `kAlwaysStatement`
2. ✅ All 7 test cases passing
3. ✅ Backward compatible (additive only)
4. ✅ Documentation in changelog

---

## Full Specification

**See:** `VERIBLE_PHASE4_ENHANCEMENT_REQUEST.md` for complete details:
- All metadata fields explained
- 7 complete examples with input/output
- Implementation guidance
- Testing requirements
- Benefits analysis

---

## Questions?

**Reference Documents:**
- Phase 3 Success: `VERIBLE_ENHANCEMENT_REQUEST.md` (expression metadata)
- Phase 4 Request: `VERIBLE_PHASE4_ENHANCEMENT_REQUEST.md` (behavioral metadata)
- Phase 3 Completion: `docs/phases/PHASE3_COMPLETE.md`

**Contact:** VeriPG team via GitHub issues

---

## Bottom Line

**Phase 3 pattern worked perfectly!** Let's repeat it for Phase 4:
- ✅ Same additive approach (`metadata` field)
- ✅ Same flattening strategy (extract key info)
- ✅ Same backward compatibility (safe)
- ✅ Same high ROI (95% code reduction)

**Request:** Implement behavioral metadata for `always` blocks before VeriPG starts Phase 4 (in ~1-2 weeks).

---

**Thank you for the amazing Phase 3 delivery! Looking forward to Phase 4 collaboration! 🚀**

