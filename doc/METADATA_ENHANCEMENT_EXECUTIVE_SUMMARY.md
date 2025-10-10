# Verible Expression Metadata Enhancement - Executive Summary

**Date:** 2025-01-10  
**Prepared For:** VeriPG Project Team  
**Status:** Ready for Implementation

---

## 1. What is Being Requested?

Add **semantic metadata** to Verible's JSON export for expression nodes, enabling tools like VeriPG to extract operation information without complex tree traversal.

### Example: Current vs. Enhanced Output

**Current JSON (requires 5-10 levels of traversal):**
```json
{
  "tag": "kBinaryExpression",
  "text": "a + b",
  "children": [
    {
      "tag": "kExpression",
      "children": [
        {
          "tag": "kReference",
          "children": [/* deep nesting to reach "a" */]
        }
      ]
    },
    {"tag": "+"},
    {
      "tag": "kExpression",
      "children": [/* deep nesting to reach "b" */]
    }
  ]
}
```

**Enhanced JSON (direct access to semantics):**
```json
{
  "tag": "kBinaryExpression",
  "text": "a + b",
  "metadata": {
    "operation": "add",
    "operator": "+",
    "operands": [
      {"role": "left", "identifier": "a", "type": "reference"},
      {"role": "right", "identifier": "b", "type": "reference"}
    ]
  },
  "children": [/* unchanged - backward compatible */]
}
```

---

## 2. Why is This Needed?

### Current VeriPG Pain Points

| Problem | Impact | Frequency |
|---------|--------|-----------|
| Complex recursive traversal code | ~300 lines of fragile parsing logic | Every expression |
| Operator position varies by type | Difficult to extract operators reliably | Every operation |
| No operand role information | Cannot distinguish left vs. right operand | All binary ops |
| Manual identifier extraction | Error-prone, requires 5-10 node hops | All operands |
| Breaks with CST changes | Frequent maintenance needed | Every Verible update |

### Benefits of Enhancement

| Benefit | Impact | Measurement |
|---------|--------|-------------|
| **Code Reduction** | ~70% less parsing code | 300 → 90 lines |
| **Reliability** | Robust against CST changes | 0 future breaks |
| **Performance** | Faster expression parsing | ~2-3x speedup |
| **Maintainability** | Simple dictionary lookup | 80% less maintenance |
| **Coverage** | Support all expression types | 100% vs. current 60% |

---

## 3. Implementation Scope

### Expression Types (Priority Order)

| Type | Priority | Examples | Complexity | Duration |
|------|----------|----------|------------|----------|
| **Binary Expressions** | HIGH | `a + b`, `x == y`, `p & q` | Medium | 3-4 days |
| **Unary Expressions** | HIGH | `~enable`, `!valid`, `-counter` | Low | 2-3 days |
| **Ternary Expressions** | HIGH | `sel ? a : b` | Medium | 2-3 days |
| **Function Calls** | MEDIUM | `$clog2(x)`, `my_func(a, b)` | Medium | 2-3 days |
| **Complex Expressions** | FUTURE | `{a, b}`, `data[7:0]` | High | TBD |

### Metadata Fields

All supported expression nodes will include:

```json
"metadata": {
  "operation": "add",           // Semantic operation name
  "operator": "+",              // Original operator symbol
  "operands": [                 // Array of operands
    {
      "role": "left",           // Operand role (left/right/condition/etc.)
      "identifier": "a",        // Variable name (null if expression)
      "type": "reference",      // reference/literal/expression
      "expression_text": "..."  // Full text if nested expression
    }
  ]
}
```

### Operation Coverage

**Binary Operations:** 24 operations
- Arithmetic: `+`, `-`, `*`, `/`, `%`, `**`
- Comparison: `==`, `!=`, `<`, `<=`, `>`, `>=`, `===`, `!==`
- Logical: `&&`, `||`
- Bitwise: `&`, `|`, `^`, `~^`, `^~`
- Shift: `<<`, `>>`, `<<<`, `>>>`

**Unary Operations:** 14 operations
- Bitwise: `~`
- Logical: `!`
- Arithmetic: `-`, `+` (unary)
- Reduction: `&`, `|`, `^`, `~&`, `~|`, `~^`, `^~`

**Ternary Operations:** 1 operation
- Conditional: `? :`

**Total:** 39 operation types

---

## 4. Implementation Plan

### Phase Breakdown

```
Phase 1: Binary Expressions (3-4 days)
  ├─ Helper functions for identifier extraction
  ├─ Operator-to-operation mapping
  ├─ Binary metadata generation
  ├─ Unit tests (10+ tests)
  └─ Integration with JSON export

Phase 2: Unary & Ternary (2-3 days)
  ├─ Unary metadata generation
  ├─ Ternary metadata generation
  ├─ Unit tests (10+ tests)
  └─ Integration test with all core types

Phase 3: Function Calls (2-3 days) [OPTIONAL]
  ├─ Function name extraction
  ├─ Argument list parsing
  ├─ Unit tests (5+ tests)
  └─ Integration

Phase 4: Testing & Documentation (3-4 days)
  ├─ Comprehensive integration test
  ├─ VeriPG integration validation
  ├─ Documentation updates
  └─ Performance benchmarking
```

**Total Duration:** 10-15 days

### Key Technical Approach

1. **Minimal Code Changes:** All changes in `verilog-tree-json.cc` and helper utilities
2. **Leverage Existing Utilities:** Use `StringSpanOfSymbol()`, `AutoUnwrapIdentifier()`, etc.
3. **Backward Compatible:** New `metadata` field is optional, doesn't affect existing fields
4. **No CST Changes:** Only JSON export is modified

---

## 5. Technical Risk Assessment

| Risk | Severity | Probability | Mitigation |
|------|----------|-------------|------------|
| Performance overhead | Medium | Low | Profile and optimize; target <5% |
| Edge case failures | Medium | Medium | Comprehensive test suite |
| Build system issues | Low | Low | Minimal dependency changes |
| VeriPG integration issues | Low | Low | Test early in Phase 2 |
| Upstream conflicts | Low | Low | Isolated changes, clear documentation |

**Overall Risk:** LOW - Well-scoped, isolated changes with clear implementation path

---

## 6. Success Criteria

### Implementation Success
- ✅ Binary expressions have complete metadata
- ✅ Unary expressions have complete metadata
- ✅ Ternary expressions have complete metadata
- ✅ All unit tests pass (25+ tests)
- ✅ No regressions in existing Verible tests
- ✅ Documentation updated

### VeriPG Integration Success
- ✅ VeriPG tests pass with enhanced binary
- ✅ VeriPG expression parsing code reduced by ~70%
- ✅ VeriPG parsing performance improves by 2-3x
- ✅ Zero fragility issues with CST structure

### Quality Metrics
- Code coverage: >90% for new metadata functions
- Test count: 25+ unit tests + 1 comprehensive integration test
- Performance impact: <5% overhead on JSON export
- Backward compatibility: 100% (no breaking changes)

---

## 7. Timeline & Milestones

| Milestone | Date | Deliverable | Verification |
|-----------|------|-------------|--------------|
| **Phase 1 Complete** | Day 4 | Binary metadata working | 10+ tests pass |
| **Phase 2 Complete** | Day 7 | All core expressions working | 20+ tests pass |
| **Phase 3 Complete** | Day 10 | Function calls (optional) | 25+ tests pass |
| **Phase 4 Complete** | Day 15 | Production ready | VeriPG integration verified |

---

## 8. Resource Requirements

### Development Resources
- **1 Developer:** Full-time for 10-15 days
- **C++ Expertise:** Required (Verible codebase)
- **Bazel Build System:** Familiarity helpful
- **SystemVerilog Knowledge:** Understanding of operators and expressions

### Testing Resources
- **Verible Test Suite:** Existing (no new infrastructure needed)
- **VeriPG Integration Test:** ~1 day to set up
- **Test Coverage Tools:** Bazel built-in

### Infrastructure
- **Build Environment:** macOS with Bazel 7.6.0
- **CI/CD:** Existing GitHub Actions (if contributing upstream)
- **No Additional Infrastructure:** All existing tools

---

## 9. Alternatives Considered

| Alternative | Pros | Cons | Decision |
|-------------|------|------|----------|
| **Separate API for data flow** | Clean separation | Requires 2 passes, memory overhead | ❌ Rejected |
| **External post-processor** | No Verible changes | Duplicates logic, fragile | ❌ Rejected |
| **Complete semantic graph** | Maximum information | Massive scope, unclear benefits | ❌ Rejected |
| **Metadata enrichment (chosen)** | Balanced effort/benefit, backward compatible | Modest implementation | ✅ **Selected** |

---

## 10. Impact Analysis

### For VeriPG

**Before Enhancement:**
```python
# Complex recursive traversal (300+ lines)
def extract_operands(expr_node):
    if expr_node.tag == "kBinaryExpression":
        left = expr_node.children[0]
        # Traverse 5-10 levels to find identifier
        left_id = traverse_to_identifier(left)  # 50+ lines
        # Repeat for right operand
        # Handle different operator positions
        # etc.
```

**After Enhancement:**
```python
# Simple metadata lookup (50 lines)
def extract_operands(expr_node):
    if 'metadata' in expr_node:
        return expr_node['metadata']['operands']
    # Fallback to old method if needed
```

**Metrics:**
- Code: 300 lines → 90 lines (70% reduction)
- Complexity: O(n) traversal → O(1) lookup
- Maintenance: High → Minimal

### For Other Tools

Any tool consuming Verible JSON benefits:
- Static analyzers
- Formal verification tools
- Code transformers
- IDE features (refactoring, navigation)
- RTL visualization tools

### For Verible Project

- **Positive:** More useful API, attracts more users
- **Minimal Cost:** ~15 days development, low maintenance
- **No Breaking Changes:** Fully backward compatible

---

## 11. Next Steps

### Immediate Actions (Before Implementation)

1. **Review & Approve:** Team reviews this plan and enhancement request
2. **Prioritize:** Confirm Phase 3 (function calls) is desired or can be deferred
3. **Assign Developer:** Allocate developer time for 10-15 days
4. **Set Up Environment:** Ensure build environment is ready

### Implementation Kickoff (Day 1)

1. Create feature branch: `feature/expression-metadata`
2. Set up test infrastructure
3. Begin Phase 1: Binary expressions
4. Daily progress updates

### Post-Implementation (Day 15+)

1. Merge to fork: `semiconductor-designs/verible`
2. Deploy to VeriPG: Copy binary and integrate
3. Measure results: Code reduction, performance, reliability
4. Consider upstream contribution: Submit PR to `chipsalliance/verible`

---

## 12. Questions & Answers

### Q: Will this break existing tools?
**A:** No. The `metadata` field is new and optional. Existing tools ignore unknown JSON fields by design.

### Q: What if identifier extraction fails?
**A:** The `identifier` field will be `null`, and the full `expression_text` will be provided as fallback.

### Q: Is function call metadata necessary?
**A:** Not critical for VeriPG's immediate needs. Can be deferred to Phase 5 if needed.

### Q: Can this be done incrementally?
**A:** Yes. After Phase 1, binary expressions will work. Each phase adds value independently.

### Q: What's the performance impact?
**A:** Estimated <5% overhead on JSON export. The identifier extraction is already done internally; we're just exposing it.

### Q: Will this help with type inference?
**A:** Not directly. Type information can be added in a future phase (Phase 6+) once type analysis is available.

---

## 13. Contacts

**Verible Enhancement:** `doc/VERIBLE_METADATA_ENHANCEMENT_PLAN.md` (full technical plan)  
**Original Request:** `doc/VERIBLE_ENHANCEMENT_REQUEST.md` (from VeriPG team)  
**Project:** VeriPG RTL Property Graph Generator

---

**Recommendation:** ✅ **APPROVE & PROCEED**

This enhancement provides significant value to VeriPG and the broader Verible ecosystem with minimal risk and reasonable implementation cost. The phased approach allows for iterative delivery and early validation.

---

*End of Executive Summary*

