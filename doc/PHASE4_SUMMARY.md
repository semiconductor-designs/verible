# Phase 4: Quick Summary

## 🎯 Goal
Add behavioral metadata to `kAlwaysStatement` nodes for clean extraction of:
- Block type (`always_ff`, `always_comb`, etc.)
- Sequential vs. combinational classification
- Clock & reset detection
- Sensitivity list extraction
- Assignment type (blocking vs. non-blocking)

## 📊 Impact
- **VeriPG Code:** 380 lines → 20 lines (95% reduction)
- **Reliability:** No fragile heuristics
- **Features Enabled:** Timing analysis, RTL synthesis verification, behavioral graphs

## 🔧 Implementation Approach

### Pattern: Same as Phase 3 Success!
1. **TDD methodology** (write tests first)
2. **Helper functions** (modular utilities)
3. **Additive metadata** (backward compatible)
4. **Phased testing** (7 test cases)

### Core Functions to Implement
```cpp
// 1. Block type detection
DetectBlockType() → "always_ff" | "always_comb" | ...

// 2. Sequential detection  
IsSequentialBlock() → true/false

// 3. Sensitivity extraction
ExtractSensitivityList() → [{name, edge}, ...]

// 4. Clock detection
DetectClock() → {signal, edge}

// 5. Reset detection
DetectReset() → {signal, type, active}

// 6. Assignment type
DetectAssignmentType() → "blocking" | "nonblocking" | "mixed"
```

### Integration Point
```cpp
void Visit(const SyntaxTreeNode &node) {
  // ... existing expression metadata ...
  
  if (tag == NodeEnum::kAlwaysStatement) {
    AddAlwaysBlockMetadata(*value_, node);  // NEW!
  }
}
```

## ✅ Test Cases (7 Required)

1. **Sequential + Async Reset** - `always_ff @(posedge clk or negedge rst_n)`
2. **Combinational** - `always_comb`
3. **Explicit Sensitivity** - `always @(a or b)`
4. **Implicit Sensitivity** - `always @*`
5. **Synchronous Reset** - `always_ff @(posedge clk) if (rst)`
6. **Latch** - `always_latch`
7. **Mixed Assignments** - Both `=` and `<=` (error case)

## 📅 Timeline

**Estimated: 3-5 days**
- **Day 1-2:** Core implementation (block type, sensitivity, clock/reset)
- **Day 3:** Testing (Tests 1-4 passing)
- **Day 4:** Edge cases (Tests 5-7 passing)
- **Day 5:** Polish & documentation

## 📈 Success Criteria

### Verible Side
- ✅ All 7 tests passing
- ✅ No existing test regressions
- ✅ 100% backward compatible
- ✅ Clean, maintainable code

### VeriPG Side
- ✅ Simple metadata extraction (~20 lines)
- ✅ Correct behavioral classification
- ✅ Clock/reset detection working
- ✅ Phase 4 behavioral graphs working

## 🚀 Ready to Start?

**Next Steps:**
1. Review implementation plan (`PHASE4_IMPLEMENTATION_PLAN.md`)
2. Create test file with 7 test cases (TDD red phase)
3. Implement helper functions
4. Make tests pass (TDD green phase)
5. Polish & document

**Confidence:** HIGH (Phase 3 pattern proven)  
**Risk:** LOW (well-defined requirements, existing CST utilities)

---

**Phase 3 delivered 37/37 tests passing. Let's make Phase 4 just as successful!** 🎯

