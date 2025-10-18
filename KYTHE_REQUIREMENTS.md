# Verible Kythe Integration - Requirements & Test Criteria

**Document Version**: 1.0  
**Date**: 2025-01-18  
**Author**: VeriPG Development Team  
**Status**: Draft - Awaiting Validation  
**Related Docs**: `VERIBLE_CAPABILITY_RESEARCH.md`, `OPENTITAN_BENCHMARK_REPORT.md`

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [Background](#background)
3. [Functional Requirements](#functional-requirements)
4. [Performance Requirements](#performance-requirements)
5. [Edge Cases & Corner Cases](#edge-cases--corner-cases)
6. [Test Criteria](#test-criteria)
7. [Acceptance Test Suite](#acceptance-test-suite)
8. [Validation Plan](#validation-plan)
9. [Success Metrics](#success-metrics)
10. [Go/No-Go Decision Criteria](#gono-go-decision-criteria)
11. [Requirement Traceability Matrix](#requirement-traceability-matrix)

---

## Executive Summary

### Purpose

Define comprehensive requirements and test criteria for integrating Verible's Kythe extractor into VeriPG's V2 extraction pipeline to provide missing dataflow edges (READS_FROM_VAR, WRITES_TO).

### Critical Need

**Current Gap**: VeriPG V2 pipeline produces 0 detections (0 FSMs, 0 CDC crossings, 0 RDC issues) across all 35 OpenTitan modules due to missing dataflow edges.

**Solution**: Leverage Verible's Kythe extractor which provides `/kythe/edge/ref` edges representing variable references - exactly what we need!

### Success Criteria

- ✅ Extract ≥95% of variable references from SystemVerilog code
- ✅ Detect ≥1 FSM in OpenTitan UART module (break_st_q)
- ✅ Detect ≥10 FSMs in OpenTitan SPI module
- ✅ Performance overhead ≤20% vs current V2 pipeline
- ✅ Zero false positives in reference extraction

---

## Background

### What is Kythe?

**Kythe** is Google's semantic code indexing system that creates a database of code relationships (definitions, references, call graphs) across programming languages.

**Verible's Kythe Extractor**: `./tools/verible/bin/verible-verilog-kythe-extractor`
- Analyzes SystemVerilog files
- Outputs JSON facts describing code structure and relationships
- Provides variable references (`/kythe/edge/ref`) - our missing dataflow edges!

### Test Results (Proof of Concept)

**32-line FSM test file**:
```
Total Kythe Facts:       154
Variable References:      21  ← Critical for dataflow!
Variable Definitions:     10
Hierarchy Edges:          10
Extraction Time:        0.1s
```

**References detected**:
- `current_state` read in case statement ✅
- `next_state` written in case branches ✅
- `clk` read in always_ff sensitivity ✅
- All enum constants (IDLE, BUSY, DONE) ✅

---

## Functional Requirements

### FR-1: Basic Variable Reference Extraction

**Priority**: P0 (Critical)  
**Requirement**: Kythe MUST extract ALL variable/signal references (reads and writes)

#### Test Case
```systemverilog
module test;
  logic [7:0] data;
  logic valid;
  
  always_comb begin
    valid = 1'b1;        // WRITE to valid
    if (valid)           // READ from valid
      data = 8'hFF;      // WRITE to data
  end
endmodule
```

#### Expected Kythe Output
- ✅ Minimum 3 `/kythe/edge/ref` edges
- ✅ References to both `valid` and `data` variables
- ✅ Distinct source locations for each reference

#### Acceptance Criteria
```python
def test_fr1_basic_variable_references():
    """FR-1: Verify Kythe extracts all variable references."""
    kythe_facts = extract_kythe('test.sv')
    ref_edges = [f for f in kythe_facts if f.get('edge_kind') == '/kythe/edge/ref']
    
    # Must have at least 3 references
    assert len(ref_edges) >= 3, f"Expected ≥3 refs, got {len(ref_edges)}"
    
    # Must reference correct variables
    target_vars = {extract_var_name(e['target']) for e in ref_edges}
    assert 'valid' in target_vars, "Missing 'valid' reference"
    assert 'data' in target_vars, "Missing 'data' reference"
    
    # Must have distinct source locations
    source_locs = {e['source']['signature'] for e in ref_edges}
    assert len(source_locs) == len(ref_edges), "Duplicate source locations"
    
    return True  # PASS
```

---

### FR-2: FSM Variable Reference Detection

**Priority**: P0 (Critical)  
**Requirement**: Kythe MUST extract references to FSM state variables

#### Test Case
```systemverilog
typedef enum logic [1:0] {IDLE, BUSY, DONE} state_t;
state_t current_state, next_state;

always_ff @(posedge clk)
  current_state <= next_state;     // READ next_state, WRITE current_state

always_comb begin
  case (current_state)              // READ current_state
    IDLE: next_state = BUSY;        // WRITE next_state, READ BUSY
    BUSY: next_state = DONE;
    DONE: next_state = IDLE;
  endcase
end
```

#### Expected Kythe Output
- ✅ At least 8 `/kythe/edge/ref` edges:
  - 1 read of `next_state` (in always_ff)
  - 1 write of `current_state` (in always_ff)
  - 1+ reads of `current_state` (in case statement)
  - 3 writes of `next_state` (in case branches)
  - 3 reads of enum constants (IDLE, BUSY, DONE)

#### Acceptance Criteria
```python
def test_fr2_fsm_references():
    """FR-2: Verify Kythe extracts FSM state variable references."""
    kythe_facts = extract_kythe('fsm.sv')
    ref_edges = [f for f in kythe_facts if f.get('edge_kind') == '/kythe/edge/ref']
    
    # Count references by variable
    refs_by_var = defaultdict(list)
    for edge in ref_edges:
        var_name = extract_var_name(edge['target'])
        refs_by_var[var_name].append(edge)
    
    # Verify state variables are referenced
    assert 'current_state' in refs_by_var, "Missing current_state references"
    assert 'next_state' in refs_by_var, "Missing next_state references"
    
    # Verify reasonable reference count (at least 2 per state variable)
    assert len(refs_by_var['current_state']) >= 2, \
        f"Too few current_state refs: {len(refs_by_var['current_state'])}"
    assert len(refs_by_var['next_state']) >= 2, \
        f"Too few next_state refs: {len(refs_by_var['next_state'])}"
    
    # Verify enum constants referenced
    enum_refs = [v for v in refs_by_var if v in ['IDLE', 'BUSY', 'DONE']]
    assert len(enum_refs) >= 2, f"Too few enum constant refs: {enum_refs}"
    
    return True  # PASS
```

---

### FR-3: Multi-Module Variable References

**Priority**: P1 (High)  
**Requirement**: Kythe MUST track references across module boundaries

#### Test Case
```systemverilog
// top.sv
module top;
  logic sig;
  sub u_sub(.in(sig));    // Reference to sig
endmodule

// sub.sv
module sub(input logic in);
  logic local;
  assign local = in;      // Reference to in
endmodule
```

#### Expected Kythe Output
- ✅ Reference to `sig` in port connection
- ✅ Reference to `in` in assignment
- ✅ Cross-file tracking (if both files parsed together)

#### Acceptance Criteria
```python
def test_fr3_cross_module_references():
    """FR-3: Verify Kythe tracks references across modules."""
    kythe_facts = extract_kythe(['top.sv', 'sub.sv'])
    ref_edges = [f for f in kythe_facts if f.get('edge_kind') == '/kythe/edge/ref']
    
    # Verify references in both modules
    refs_in_top = [e for e in ref_edges if 'top.sv' in e['source']['path']]
    refs_in_sub = [e for e in ref_edges if 'sub.sv' in e['source']['path']]
    
    assert len(refs_in_top) >= 1, "No references found in top.sv"
    assert len(refs_in_sub) >= 1, "No references found in sub.sv"
    
    return True  # PASS
```

---

### FR-4: Location Accuracy

**Priority**: P0 (Critical)  
**Requirement**: Kythe anchors MUST provide accurate source locations for mapping to CST nodes

#### Test Case
```systemverilog
// Line 1: module test;
// Line 2:   logic sig;
// Line 3:   assign sig = 1'b0;  // Reference at column 10-13
// Line 4: endmodule
```

#### Expected Kythe Output
- ✅ Anchor for `sig` reference with:
  - Byte offset matching "sig" in assignment (line 3)
  - Convertible to line:column (3, 10)
  - Text extraction yields "sig"

#### Acceptance Criteria
```python
def test_fr4_location_accuracy():
    """FR-4: Verify Kythe provides accurate source locations."""
    source = "module test;\n  logic sig;\n  assign sig = 1'b0;\nendmodule\n"
    with open('test.sv', 'w') as f:
        f.write(source)
    
    kythe_facts = extract_kythe('test.sv')
    ref_edges = [f for f in kythe_facts if f.get('edge_kind') == '/kythe/edge/ref']
    
    # Find reference to 'sig' in assignment
    sig_ref = next((e for e in ref_edges if extract_var_name(e['target']) == 'sig'), None)
    assert sig_ref is not None, "sig reference not found"
    
    # Extract location from anchor signature: "@29:32#"
    anchor_sig = sig_ref['source']['signature']
    byte_start, byte_end = parse_anchor(anchor_sig)
    
    # Verify location matches "sig" in source
    actual_text = source[byte_start:byte_end]
    assert actual_text == 'sig', f"Location mismatch: expected 'sig', got '{actual_text}'"
    
    # Verify line:column conversion
    line, col = byte_offset_to_line_col(source, byte_start)
    assert line == 3, f"Wrong line: expected 3, got {line}"
    assert 8 <= col <= 12, f"Wrong column: expected ~10, got {col}"
    
    return True  # PASS
```

---

### FR-5: Hierarchical References

**Priority**: P2 (Medium)  
**Requirement**: Kythe SHOULD track hierarchical signal references (instance.signal)

#### Test Case
```systemverilog
module top;
  sub u_sub();
  logic result;
  assign result = u_sub.internal_sig;  // Hierarchical reference
endmodule

module sub;
  logic internal_sig;
endmodule
```

#### Expected Kythe Output
- ✅ Best case: Reference to `u_sub.internal_sig`
- ⚠️ Acceptable: Reference to `u_sub` instance only
- ❌ Fail: No reference at all

#### Acceptance Criteria
```python
def test_fr5_hierarchical_references():
    """FR-5: Verify Kythe handles hierarchical references (may have limitations)."""
    kythe_facts = extract_kythe('hierarchical.sv')
    ref_edges = [f for f in kythe_facts if f.get('edge_kind') == '/kythe/edge/ref']
    
    # Look for any reference involving 'u_sub' or 'internal_sig'
    hierarchical_refs = [e for e in ref_edges 
                        if 'u_sub' in str(e) or 'internal_sig' in str(e)]
    
    # At minimum, should reference the instance
    if len(hierarchical_refs) >= 1:
        return True  # PASS
    else:
        warnings.warn("No hierarchical references found - may be Kythe limitation")
        return "PARTIAL"  # Acceptable limitation
```

---

### FR-6: Array and Struct References

**Priority**: P2 (Medium)  
**Requirement**: Kythe SHOULD track references to array and struct base variables

#### Test Case
```systemverilog
logic [7:0] arr [4];
struct packed {
  logic valid;
  logic [7:0] data;
} pkt;

assign arr[0] = 8'hAA;     // Array element reference
assign pkt.valid = 1'b1;   // Struct member reference
```

#### Expected Kythe Output
- ✅ Reference to `arr` (base array)
- ✅ Reference to `pkt` (base struct)
- ⚠️ May not track individual element/member access (acceptable)

#### Acceptance Criteria
```python
def test_fr6_complex_types():
    """FR-6: Verify Kythe handles arrays and structs."""
    kythe_facts = extract_kythe('complex_types.sv')
    ref_edges = [f for f in kythe_facts if f.get('edge_kind') == '/kythe/edge/ref']
    
    refs_by_var = {extract_var_name(e['target']): e for e in ref_edges}
    
    # At minimum, base variables should be referenced
    assert 'arr' in refs_by_var, "Array base not referenced"
    assert 'pkt' in refs_by_var, "Struct base not referenced"
    
    return True  # PASS
```

---

## Performance Requirements

### PR-1: Extraction Speed

**Priority**: P0 (Critical)  
**Requirement**: Kythe extraction MUST NOT significantly slow down pipeline

#### Acceptance Criteria

| File Size | Line Count | Max Time | Notes |
|-----------|------------|----------|-------|
| Small | 100 lines | 0.5s | Typical module |
| Medium | 500 lines | 2.0s | Large module |
| Large | 2000 lines | 10.0s | Very large (rare) |
| **OpenTitan Full** | **504 files** | **5 minutes** | **Production target** |

#### Test Implementation
```python
def test_pr1_extraction_speed():
    """PR-1: Verify Kythe extraction performance."""
    test_cases = [
        ('small_100.sv', 100, 0.5),
        ('medium_500.sv', 500, 2.0),
        ('large_2000.sv', 2000, 10.0),
    ]
    
    for filename, line_count, max_time in test_cases:
        generate_sv_file(filename, line_count)
        
        start = time.time()
        kythe_facts = extract_kythe(filename)
        elapsed = time.time() - start
        
        assert elapsed < max_time, \
            f"{filename} took {elapsed:.2f}s (max {max_time}s)"
        
        # Verify facts were actually extracted
        assert len(kythe_facts) > 0, f"No facts extracted from {filename}"
    
    return True  # PASS
```

---

### PR-2: Memory Efficiency

**Priority**: P1 (High)  
**Requirement**: Kythe extraction MUST handle large files without excessive memory usage

#### Acceptance Criteria
- Peak memory usage < 500 MB for single file
- Supports streaming (doesn't load entire file in memory)
- Memory usage grows linearly with file size (not exponential)

#### Test Implementation
```python
def test_pr2_memory_usage():
    """PR-2: Verify Kythe memory efficiency."""
    import psutil
    
    process = psutil.Process()
    mem_before = process.memory_info().rss / 1024 / 1024  # MB
    
    # Extract from large file
    kythe_facts = extract_kythe('large_2000_lines.sv')
    
    mem_after = process.memory_info().rss / 1024 / 1024  # MB
    mem_used = mem_after - mem_before
    
    assert mem_used < 500, f"Memory usage too high: {mem_used:.1f} MB"
    
    return True  # PASS
```

---

## Edge Cases & Corner Cases

### EC-1: Empty Modules

**Test Case**:
```systemverilog
module empty;
endmodule
```

**Expected**: No crash, no references, valid Kythe JSON output

**Acceptance**: Graceful handling, empty fact list OK

---

### EC-2: Parameterized Modules

**Test Case**:
```systemverilog
module param #(parameter WIDTH = 8) (input logic [WIDTH-1:0] data);
  assign data = '0;
endmodule
```

**Expected**: References to `WIDTH` parameter and `data` port

**Acceptance**: Both parameter and port usage tracked

---

### EC-3: Generate Blocks

**Test Case**:
```systemverilog
generate
  for (genvar i = 0; i < 4; i++) begin
    logic sig;
    assign sig = 1'b0;  // Reference inside generate
  end
endgenerate
```

**Expected**: References inside generate blocks tracked

**Acceptance**: At least base `sig` variable tracked (index may be missing)

---

### EC-4: Macro Expansions

**Test Case**:
```systemverilog
`define ASSIGN(dst, src) assign dst = src

logic a, b;
`ASSIGN(a, b)  // Macro expansion
```

**Expected**: 
- Best case: References after macro expansion
- Acceptable: References to unexpanded macro
- Fail: No references at all

**Acceptance**: At least unexpanded macro tracked

---

### EC-5: Circular References

**Test Case**:
```systemverilog
logic a, b;
assign a = b;
assign b = a;  // Circular dependency!
```

**Expected**: Both references tracked without infinite loop

**Acceptance**: Extraction completes without timeout/crash

---

### EC-6: Syntax Errors

**Test Case**:
```systemverilog
module broken
  logic sig;  // Missing semicolon
  assign sig = 1'b0;
endmodule
```

**Expected**: 
- Kythe reports error gracefully
- May extract partial facts (best effort)

**Acceptance**: No crash, error message provided

---

## Test Criteria

### Test Organization

```
tests/kythe_integration/
├── test_kythe_basic.py              # FR-1: Basic variable references
├── test_kythe_fsm.py                # FR-2: FSM-specific patterns
├── test_kythe_multi_module.py       # FR-3: Cross-module tracking
├── test_kythe_location.py           # FR-4: Location accuracy
├── test_kythe_hierarchical.py       # FR-5: Hierarchical references
├── test_kythe_complex_types.py      # FR-6: Arrays, structs
├── test_kythe_performance.py        # PR-1, PR-2: Performance
├── test_kythe_edge_cases.py         # EC-1 to EC-6: Edge cases
├── test_kythe_opentitan.py          # Integration: Real-world validation
├── kythe_test_helpers.py            # Shared helper functions
└── fixtures/
    ├── simple_var.sv
    ├── fsm.sv
    ├── multi_module/
    │   ├── top.sv
    │   └── sub.sv
    ├── hierarchical.sv
    ├── complex_types.sv
    └── edge_cases/
        ├── empty.sv
        ├── parameterized.sv
        ├── generate.sv
        ├── macro.sv
        ├── circular.sv
        └── syntax_error.sv
```

---

## Acceptance Test Suite

### Master Acceptance Test Structure

The master acceptance test (`test_kythe_acceptance.py`) orchestrates all validation:

1. **Functional Requirements** (FR-1 to FR-6)
2. **Performance Requirements** (PR-1 to PR-2)
3. **Edge Cases** (EC-1 to EC-6)
4. **OpenTitan Smoke Test** (Real-world validation)

**Pass Criteria**:
- All P0 (Critical) requirements: 100% pass
- All P1 (High) requirements: ≥90% pass
- All P2 (Medium) requirements: ≥80% pass
- OpenTitan smoke test: Pass

---

## Validation Plan

### Phase 1: Synthetic Tests (Day 1)

**Objective**: Validate Kythe on controlled test fixtures

**Steps**:
1. Create minimal test fixtures for each FR (FR-1 to FR-6)
2. Run Verible Kythe extractor on each fixture
3. Validate output against expected facts
4. Document any gaps or limitations

**Deliverables**:
- Test fixtures in `tests/kythe_integration/fixtures/`
- Test results report
- Gap analysis document (if any failures)

**Success Criteria**:
- ✅ FR-1, FR-2, FR-4 pass 100% (critical)
- ✅ FR-3, FR-5, FR-6 pass ≥80% (acceptable with limitations)

---

### Phase 2: OpenTitan Subset (Day 2)

**Objective**: Validate on real-world SystemVerilog (UART module)

**Steps**:
1. Run Kythe extractor on `uart_core.sv`
2. Count total references extracted
3. Spot-check 10 random references for accuracy
4. Measure extraction time and memory

**Expected Results**:
- Total references: ≥50 (UART has ~691 nodes, expect similar refs)
- Accuracy: ≥95% spot-check correct
- Time: <1 second
- Memory: <100 MB

**Success Criteria**:
- ✅ Extract ≥50 references
- ✅ ≥90% accuracy on spot-checks
- ✅ Performance acceptable

---

### Phase 3: Full OpenTitan (Day 3)

**Objective**: Validate scalability across all 35 OpenTitan modules

**Steps**:
1. Run Kythe extractor on all 504 OpenTitan files
2. Aggregate statistics (total refs, avg per file)
3. Identify outliers (modules with 0 refs = potential problems)
4. Performance validation (total time <5 min)

**Expected Results**:
- Total references: ≥5,000 across 504 files
- Average: ~10 refs/file (varies by module size)
- Outliers: <5% modules with 0 refs
- Total time: <300 seconds

**Success Criteria**:
- ✅ Extract ≥5,000 total references
- ✅ <10% modules with 0 refs
- ✅ Performance ≤5 minutes

---

### Phase 4: Integration Proof of Concept (Day 4)

**Objective**: Build KytheAdapter and detect first FSM

**Steps**:
1. Implement `KytheAdapter` class
2. Convert Kythe facts → VeriPG edges (READS_FROM_VAR)
3. Merge with V2 pipeline output
4. Run FSMAnalyzer on UART

**Expected Results**:
- KytheAdapter successfully parses Kythe JSON
- Creates ≥50 READS_FROM_VAR edges for UART
- FSMAnalyzer detects 1 FSM: `break_st_q`

**Success Criteria**:
- ✅ KytheAdapter builds valid VeriPG edges
- ✅ FSM detected in UART module
- ✅ No false positives

---

## Success Metrics

### Minimum Viable Product (MVP)

**GO Decision Criteria**:
- ✅ FR-1, FR-2, FR-4: Pass 100% (critical for FSM/CDC)
- ⚠️ FR-3, FR-5, FR-6: Pass ≥80% (nice-to-have, limitations acceptable)
- ✅ PR-1: Pass 100% (performance critical)
- ✅ OpenTitan smoke test: Pass

**If MVP criteria met**: Proceed with Kythe integration (Option C or Option A)

---

### Production Ready

**Full Deployment Criteria**:
- ✅ All FR (FR-1 to FR-6): Pass 100%
- ✅ All PR (PR-1 to PR-2): Pass 100%
- ✅ All EC (EC-1 to EC-6): Pass ≥90%
- ✅ OpenTitan full: Extract ≥5,000 references across 35 modules
- ✅ Zero false positives in reference extraction
- ✅ FSM detection: ≥11 FSMs (UART + SPI combined)

---

## Go/No-Go Decision Criteria

### GO Criteria (Proceed with Kythe integration)

| Criterion | Threshold | Measurement |
|-----------|-----------|-------------|
| **FR-1: Variable refs** | ≥95% extraction rate | Synthetic test pass rate |
| **FR-2: FSM refs** | ≥90% extraction rate | FSM test pass rate |
| **FR-4: Location accuracy** | ≥98% accuracy | Location validation |
| **PR-1: Performance** | ≤5min for OpenTitan | Timed benchmark |
| **OpenTitan UART** | ≥50 references | Actual extraction |
| **No crashes** | 100% stability | Error rate |

**Decision**: If ALL criteria met → **GO** (proceed with integration)

---

### NO-GO Criteria (Build custom dataflow instead)

| Criterion | Threshold | Impact |
|-----------|-----------|--------|
| **FR-1: Variable refs** | <80% extraction | Critical - can't detect dataflow |
| **FR-2: FSM refs** | <70% extraction | Critical - FSM detection fails |
| **FR-4: Location accuracy** | <90% accuracy | Critical - can't map to CST |
| **PR-1: Performance** | >10min for OpenTitan | Unacceptable overhead |
| **Frequent crashes** | >5% error rate | Unstable |

**Decision**: If ANY critical criterion fails → **NO-GO** (build custom solution)

---

## Requirement Traceability Matrix

| Req ID | Description | Priority | Test File | Expected Outcome | Actual | Status |
|--------|-------------|----------|-----------|------------------|--------|--------|
| FR-1 | Basic variable refs | P0 | test_kythe_basic.py | ≥95% extraction | TBD | 🔲 To validate |
| FR-2 | FSM variable refs | P0 | test_kythe_fsm.py | ≥90% extraction | TBD | 🔲 To validate |
| FR-3 | Multi-module refs | P1 | test_kythe_multi_module.py | ≥80% extraction | TBD | 🔲 To validate |
| FR-4 | Location accuracy | P0 | test_kythe_location.py | ≥98% accuracy | TBD | 🔲 To validate |
| FR-5 | Hierarchical refs | P2 | test_kythe_hierarchical.py | Best effort | TBD | 🔲 To validate |
| FR-6 | Complex types | P2 | test_kythe_complex_types.py | Base vars tracked | TBD | 🔲 To validate |
| PR-1 | Extraction speed | P0 | test_kythe_performance.py | ≤5min OpenTitan | TBD | 🔲 To validate |
| PR-2 | Memory usage | P1 | test_kythe_performance.py | <500 MB peak | TBD | 🔲 To validate |
| EC-1 | Empty modules | P2 | test_kythe_edge_cases.py | No crash | TBD | 🔲 To validate |
| EC-2 | Parameterized | P2 | test_kythe_edge_cases.py | Refs tracked | TBD | 🔲 To validate |
| EC-3 | Generate blocks | P2 | test_kythe_edge_cases.py | Refs tracked | TBD | 🔲 To validate |
| EC-4 | Macros | P2 | test_kythe_edge_cases.py | Best effort | TBD | 🔲 To validate |
| EC-5 | Circular refs | P2 | test_kythe_edge_cases.py | No crash | TBD | 🔲 To validate |
| EC-6 | Syntax errors | P2 | test_kythe_edge_cases.py | Graceful error | TBD | 🔲 To validate |

**Legend**:
- 🔲 To validate - Not yet tested
- ✅ PASS - Requirement met
- ⚠️ PARTIAL - Partial compliance (acceptable with limitations)
- ❌ FAIL - Requirement not met

---

## Appendix A: Helper Functions Reference

See `tests/kythe_integration/kythe_test_helpers.py` for implementation of:

- `extract_kythe(file_or_files)` - Run Verible Kythe extractor
- `extract_var_name(target_dict)` - Parse variable name from Kythe target
- `parse_anchor(anchor_sig)` - Convert anchor to byte offsets
- `byte_offset_to_line_col(source, offset)` - Convert byte offset to line:column
- `generate_sv_file(filename, line_count)` - Generate test fixtures

---

## Appendix B: Kythe Fact Example

**Input SystemVerilog**:
```systemverilog
state_t current_state;
case (current_state)
  IDLE: ...
endcase
```

**Kythe Output**:
```json
{
  "source": {
    "signature": "@185:198#",
    "path": "fsm.sv",
    "language": "verilog"
  },
  "edge_kind": "/kythe/edge/ref",
  "target": {
    "signature": "/path/fsm.sv#test_fsm#current_state#",
    "path": "fsm.sv",
    "language": "verilog"
  }
}
```

**Interpretation**:
- Source location: bytes 185-198 in fsm.sv
- Edge type: Variable reference
- Target: Variable `current_state` in module `test_fsm`

---

## Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-01-18 | VeriPG Team | Initial requirements document |

---

**Status**: ✅ Ready for validation  
**Next Step**: Run Phase 1 validation (synthetic tests)  
**Ping when ready to proceed**: Implementation awaits validation results

