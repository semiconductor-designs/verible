# Verible Enhancement Request: SystemVerilog Assertion (SVA) Support

**Request Date:** October 12, 2025  
**Requestor:** VeriPG Project (SystemVerilog Property Graph Generator)  
**Priority:** HIGH  
**Impact:** Enables verification code analysis for millions of SystemVerilog designs  

> **📋 NOTE:** This is a detailed request for SVA support only. For a comprehensive view of ALL verification feature gaps (SVA + DPI + Program Blocks + Coverage), see [`VERIBLE_ENHANCEMENT_REQUEST_VERIFICATION_COMPLETE.md`](./VERIBLE_ENHANCEMENT_REQUEST_VERIFICATION_COMPLETE.md)  

---

## 🎯 Executive Summary

**Request:** Add full parsing support for SystemVerilog Assertions (SVA) as defined in IEEE 1800-2017 Chapter 16.

**Current Status:** Verible v2.0.0 returns `null` (parse failure) for any code containing assertion statements.

**Business Impact:**
- **Blocks** extraction of verification constructs used in 90%+ of modern SystemVerilog testbenches
- **Prevents** formal verification tool integration
- **Limits** VeriPG from analyzing UVM/OVM verification code
- **Affects** OpenTitan and other major open-source projects

**Estimated Benefit:** Enables analysis of ~15-20 IEEE keywords (6-8% of language coverage)

---

## 🚨 Current Limitation - Demonstrated

### Test Case 1: Simplest Possible Assertion
```systemverilog
module test;
  logic data_valid;
  always_comb begin
    assert (data_valid);  // ← Parse fails
  end
endmodule
```

**Verible Result:**
```bash
$ verible-verilog-syntax --export_json test.sv
{
  "test.sv": null  ← Parse failure!
}
```

### Test Case 2: Immediate Assertion with Action
```systemverilog
module test2;
  logic [7:0] data;
  always_comb begin
    assert (data < 100) 
      else $error("Data out of range");  // ← Parse fails
  end
endmodule
```

**Verible Result:** `null` (parse failure)

### Test Case 3: Assumption
```systemverilog
module test3;
  logic rst_n;
  always_comb begin
    assume (rst_n == 1'b0);  // ← Parse fails
  end
endmodule
```

**Verible Result:** `null` (parse failure)

---

## 📋 Feature Request Details

### Phase 1: Immediate Assertions (CRITICAL - Highest Priority)

**IEEE Reference:** IEEE 1800-2017 Section 16.3 - Immediate Assertions

**Keywords Required:**
1. ✅ `assert` - Assertion statement
2. ✅ `assume` - Assumption statement (formal verification)
3. ✅ `cover` - Coverage statement

**Syntax Patterns:**

```systemverilog
// Pattern 1: Basic immediate assertion
assert ( expression ) ;

// Pattern 2: Assertion with action block
assert ( expression ) action_block ;

// Pattern 3: Assertion with pass/fail actions
assert ( expression ) pass_statement else fail_statement ;

// Pattern 4: Labeled assertion
label : assert ( expression ) else fail_statement ;

// Pattern 5: With severity
assert ( expression ) else $fatal ( message ) ;
assert ( expression ) else $error ( message ) ;
assert ( expression ) else $warning ( message ) ;
assert ( expression ) else $info ( message ) ;
```

**Real-World Examples:**
```systemverilog
// Example 1: Range check (from RTL code)
always_comb begin
  assert (addr < MAX_ADDR) 
    else $fatal("Address %0d exceeds MAX_ADDR", addr);
end

// Example 2: State machine invariant
always_ff @(posedge clk) begin
  assert (state inside {IDLE, BUSY, DONE})
    else $error("Invalid state: %0d", state);
end

// Example 3: Protocol check
always_comb begin
  assert (valid |-> ready)
    else $error("Valid without ready");
end

// Example 4: Formal verification assumption
always_comb begin
  assume (rst_n == 1'b0 || initialized)
    else $error("Uninitialized state");
end

// Example 5: Functional coverage point
always_ff @(posedge clk) begin
  cover (state == IDLE && req);
end
```

**Required CST Nodes:**

```
kImmediateAssertion
  ├─ kAssertionKeyword ("assert" | "assume" | "cover")
  ├─ "("
  ├─ kExpression (assertion condition)
  ├─ ")"
  ├─ [optional] kActionBlock
  │   ├─ [optional] kPassStatement
  │   ├─ "else"
  │   └─ kFailStatement
  │       └─ kSystemTaskCall ($error, $fatal, $warning, $info)
  └─ ";"
```

**Test Cases Needed:**
- ✅ Basic `assert(expr);`
- ✅ `assert(expr) else $error(...);`
- ✅ `assume(expr);`
- ✅ `cover(expr);`
- ✅ Labeled assertions: `label: assert(expr);`
- ✅ Multiple assertions in one block
- ✅ Assertions in always_comb
- ✅ Assertions in always_ff
- ✅ Assertions in initial blocks
- ✅ Assertions in functions/tasks

---

### Phase 2: Concurrent Assertions (HIGH Priority)

**IEEE Reference:** IEEE 1800-2017 Section 16.5-16.12

**Keywords Required:**
1. ✅ `property` / `endproperty` - Property declarations
2. ✅ `sequence` / `endsequence` - Sequence declarations
3. ✅ `expect` - Expect statement

**Syntax Patterns:**

```systemverilog
// Pattern 1: Property declaration
property property_name [ ( formal_port_list ) ] ;
  property_spec
endproperty

// Pattern 2: Concurrent assertion
assert property ( property_expr ) action_block ;

// Pattern 3: Inline property
assert property ( @(posedge clk) disable iff (rst)
  req |-> ##1 ack ) else $error(...);

// Pattern 4: Sequence declaration
sequence sequence_name [ ( formal_port_list ) ] ;
  sequence_expr
endsequence
```

**Real-World Examples:**
```systemverilog
// Example 1: Request-acknowledge protocol
property p_req_ack;
  @(posedge clk) disable iff (rst)
  req |-> ##[1:3] ack;
endproperty

assert property (p_req_ack) 
  else $error("Request not acknowledged");

// Example 2: FIFO full/empty mutual exclusion
property p_fifo_mutex;
  @(posedge clk)
  !(full && empty);
endproperty

assert property (p_fifo_mutex);

// Example 3: Handshake sequence
sequence s_handshake;
  @(posedge clk) valid ##1 ready;
endsequence

property p_data_stable;
  @(posedge clk)
  s_handshake |-> $stable(data);
endproperty

assert property (p_data_stable);

// Example 4: AXI protocol check
property p_axi_valid_stable;
  @(posedge aclk) disable iff (!aresetn)
  $rose(awvalid) |-> awvalid throughout ##[0:$] awready;
endproperty

cover property (p_axi_valid_stable);
```

**Required CST Nodes:**

```
kPropertyDeclaration
  ├─ "property"
  ├─ kPropertyIdentifier
  ├─ [optional] kFormalPortList
  ├─ ";"
  ├─ kPropertySpec
  │   ├─ [optional] kClockingEvent
  │   ├─ [optional] "disable" "iff" kExpression
  │   └─ kPropertyExpr (with temporal operators)
  └─ "endproperty"

kSequenceDeclaration
  ├─ "sequence"
  ├─ kSequenceIdentifier
  ├─ [optional] kFormalPortList
  ├─ ";"
  ├─ kSequenceExpr
  └─ "endsequence"

kConcurrentAssertion
  ├─ kAssertionKeyword ("assert" | "assume" | "cover")
  ├─ "property"
  ├─ "("
  ├─ kPropertyExpr
  ├─ ")"
  └─ [optional] kActionBlock
```

---

### Phase 3: Temporal Operators (MEDIUM Priority)

**IEEE Reference:** IEEE 1800-2017 Section 16.9-16.10

**Operators Required:**

**Delay Operators:**
- `##n` - Fixed delay
- `##[m:n]` - Range delay
- `##[m:$]` - Unbounded delay

**Implication Operators:**
- `|->` - Overlapped implication
- `|=>` - Non-overlapped implication

**Repetition Operators:**
- `[*n]` - Consecutive repetition
- `[*m:n]` - Range repetition
- `[*]` - Zero or more repetition
- `[+]` - One or more repetition
- `[=n]` - Goto repetition
- `[->n]` - Non-consecutive goto repetition

**Logical Operators:**
- `and`, `or`, `not` - Boolean
- `throughout` - Throughout
- `within` - Within
- `intersect` - Intersect
- `first_match` - First match

**Real-World Examples:**
```systemverilog
// Delay operators
property p_delay;
  req ##2 ack;           // Exactly 2 cycles
endproperty

property p_range;
  req ##[1:5] ack;       // 1 to 5 cycles
endproperty

// Implication
property p_imply;
  req |-> ##1 gnt;       // If req, then gnt next cycle
endproperty

// Repetition
property p_repeat;
  start |=> data[*4] ##1 done;  // 4 consecutive data cycles
endproperty

// Eventually
property p_eventually;
  req |-> ##[0:$] ack;   // ack eventually happens
endproperty

// Throughout
property p_throughout;
  start |=> busy throughout ##[1:10] done;
endproperty
```

---

### Phase 4: Advanced Features (LOW Priority - Can Defer)

**Checkers:**
- `checker` / `endchecker`
- Reusable verification components

**Local Variables:**
- Local variable declarations in properties
- `var`, `logic` inside properties

**Formal Arguments:**
- Property/sequence formal arguments
- `input`, `output`, `inout` in property ports

**System Functions:**
- `$rose()`, `$fell()`, `$stable()`, `$past()`
- `$onehot()`, `$onehot0()`, `$isunknown()`
- `$countones()`, `$sampled()`

---

## 🎯 Use Cases

### Use Case 1: RTL Assertion Analysis (VeriPG)
**Scenario:** Extract and analyze assertions embedded in RTL code for design verification

```systemverilog
module fifo #(parameter DEPTH = 16) (
  input  logic clk, rst_n, push, pop,
  output logic full, empty
);
  
  logic [$clog2(DEPTH):0] count;
  
  // RTL assertions for design invariants
  always_comb begin
    assert (count <= DEPTH) 
      else $fatal("FIFO overflow");
    
    assert (!(full && push)) 
      else $error("Push to full FIFO");
    
    assert (!(empty && pop)) 
      else $error("Pop from empty FIFO");
  end
  
  // Coverage of corner cases
  always_ff @(posedge clk) begin
    cover (full && !push);
    cover (empty && !pop);
  end
  
endmodule
```

**VeriPG Needs:**
- Extract all assertion/assume/cover nodes
- Link assertions to parent modules/blocks
- Capture assertion conditions for analysis
- Generate assertion coverage reports

### Use Case 2: Formal Verification Integration
**Scenario:** Extract properties for formal verification tools (JasperGold, Questa Formal)

```systemverilog
module axi_slave (
  input  logic aclk, aresetn,
  input  logic awvalid, wvalid,
  output logic awready, wready
);
  
  // Formal assumptions (environment constraints)
  property p_reset_behavior;
    @(posedge aclk)
    !aresetn |-> (!awvalid && !wvalid);
  endproperty
  
  assume property (p_reset_behavior);
  
  // Formal assertions (design requirements)
  property p_handshake;
    @(posedge aclk) disable iff (!aresetn)
    awvalid && !awready |=> awvalid;
  endproperty
  
  assert property (p_handshake);
  
endmodule
```

**Integration Needs:**
- Export properties to formal tools
- Distinguish assumptions from assertions
- Preserve temporal relationships

### Use Case 3: UVM Testbench Analysis
**Scenario:** Analyze assertions in UVM verification components

```systemverilog
class axi_monitor extends uvm_monitor;
  
  // Concurrent assertions in monitor
  property p_axi_protocol;
    @(posedge vif.aclk) disable iff (!vif.aresetn)
    vif.awvalid && vif.awready |-> ##1 vif.wvalid;
  endproperty
  
  assert property (p_axi_protocol)
    else `uvm_error("AXI_MON", "Protocol violation");
  
  // Coverage of protocol scenarios
  cover property (@(posedge vif.aclk)
    vif.awvalid ##1 vif.wvalid ##1 vif.bvalid);
  
endclass
```

### Use Case 4: OpenTitan Integration
**Scenario:** VeriPG needs to analyze OpenTitan's extensive use of assertions

**OpenTitan Statistics:**
- **Estimated Assertions:** 2,000+ across 100+ IP blocks
- **Coverage Points:** 5,000+ cover statements
- **Properties:** 500+ reusable properties

**Example from OpenTitan UART:**
```systemverilog
module uart_core (
  input clk_i, rst_ni,
  input rx_i,
  output tx_o
);
  
  // Protocol assertions
  assert property (@(posedge clk_i) disable iff (!rst_ni)
    tx_start |-> ##10 tx_done)
    else $error("TX timeout");
  
  // State invariants
  always_comb begin
    assert (!(tx_busy && tx_idle))
      else $fatal("Invalid TX state");
  end
  
endmodule
```

---

## 💡 Implementation Suggestions

### Approach 1: Minimal Support (Quick Win)
**Timeline:** 2-4 weeks  
**Scope:** Immediate assertions only

**Deliverables:**
1. Parse `assert(expr);` statements
2. Parse `assume(expr);` statements
3. Parse `cover(expr);` statements
4. Handle action blocks (`else $error(...)`)
5. Support labeled assertions

**CST Changes:**
- Add `kImmediateAssertion` node type
- Add `kAssertionKeyword` token
- Extend statement parsing to recognize assertion statements

**Testing:**
- Add 20+ test cases for immediate assertions
- Validate with OpenTitan examples
- Ensure backward compatibility

**Value:** Unblocks 80% of VeriPG use cases (RTL assertions)

---

### Approach 2: Comprehensive Support (Full Solution)
**Timeline:** 2-3 months  
**Scope:** Immediate + concurrent assertions + properties/sequences

**Deliverables:**
1. All immediate assertion support (Approach 1)
2. `property...endproperty` declarations
3. `sequence...endsequence` declarations
4. Concurrent assertion parsing
5. Temporal operator recognition
6. Clocking events in assertions

**CST Changes:**
- Add `kPropertyDeclaration`, `kSequenceDeclaration` nodes
- Add `kConcurrentAssertion` node type
- Add temporal operator tokens (`|->`, `|=>`, `##`, etc.)
- Extend expression parsing for temporal operators

**Testing:**
- Add 100+ test cases covering all SVA features
- Validate with UVM testbenches
- OpenTitan validation

**Value:** Enables complete verification code analysis (100% SVA coverage)

---

### Approach 3: Incremental Rollout (Recommended)
**Timeline:** 6-8 weeks (phased)  
**Scope:** Prioritized by usage frequency

**Phase 1 (Weeks 1-2): Immediate Assertions**
- Parse `assert`, `assume`, `cover` statements
- Handle simple action blocks
- **Delivers:** 80% of use cases

**Phase 2 (Weeks 3-4): Basic Properties**
- Parse `property...endproperty`
- Parse `assert property(...)` 
- Handle clocking events
- **Delivers:** 95% of use cases

**Phase 3 (Weeks 5-6): Sequences & Temporal**
- Parse `sequence...endsequence`
- Add temporal operator support
- **Delivers:** 99% of use cases

**Phase 4 (Weeks 7-8): Advanced Features**
- Property formal arguments
- System functions in properties
- Checkers (if time permits)
- **Delivers:** 100% coverage

---

## 📊 Impact Assessment

### Quantitative Impact

**VeriPG Project:**
- Unblocks Phase 8 implementation (~15 keywords)
- Enables 6-8% additional language coverage
- Required for OpenTitan analysis (2,000+ assertions)

**Broader Community:**
- **Estimated Users:** Every SystemVerilog verification engineer
- **Industry Tools:** Formal verification, lint tools, documentation generators
- **Open Source Projects:** OpenTitan, PULP, LowRISC, etc.

### Qualitative Impact

**Verification Methodology:**
- Enables property-based verification analysis
- Supports assertion-based design methodology
- Integrates with formal verification tools

**Code Quality:**
- Allows static analysis of assertions
- Enables assertion coverage tracking
- Supports design intent documentation

**Ecosystem:**
- Makes Verible more competitive with commercial parsers
- Attracts verification-focused users
- Strengthens open-source SystemVerilog tooling

---

## 🔗 References

### IEEE Standards
- **IEEE 1800-2017:** SystemVerilog Language Reference Manual
  - Chapter 16: Assertions
  - Section 16.3: Immediate Assertions
  - Section 16.5-16.12: Concurrent Assertions

### Industry Resources
- **Accellera SVA Tutorial:** Comprehensive SVA guide
- **Mentor Graphics SVA Guide:** Best practices
- **Cadence Formal Verification:** Tool integration examples

### Similar Parsers
- **Synopsys VCS:** Full SVA support
- **Mentor Questa:** Complete assertion parsing
- **Cadence Xcelium:** Comprehensive SVA coverage

**Note:** Verible is currently the only major open-source parser lacking SVA support.

---

## 📝 Acceptance Criteria

### Minimum Viable Product (MVP)
- ✅ Parse all immediate assertion statements without returning `null`
- ✅ Extract assertion keyword (`assert`, `assume`, `cover`)
- ✅ Extract assertion condition expression
- ✅ Extract action blocks (`else $error(...)`)
- ✅ Support labeled assertions
- ✅ Provide CST nodes for downstream tools
- ✅ Pass 20+ test cases

### Full Feature Set
- ✅ All MVP criteria
- ✅ Parse `property...endproperty` declarations
- ✅ Parse `sequence...endsequence` declarations
- ✅ Parse concurrent assertions
- ✅ Recognize temporal operators
- ✅ Handle clocking events
- ✅ Pass 100+ test cases
- ✅ Zero regression on existing Verible test suite

---

## 🤝 Collaboration Offer

**VeriPG Team Offers:**

1. **Test Cases:** Provide 100+ real-world SVA examples from OpenTitan
2. **Validation:** Test every Verible release candidate with VeriPG suite
3. **Documentation:** Contribute SVA parsing documentation
4. **Feedback:** Rapid feedback on implementation approaches
5. **Co-Development:** Can contribute to implementation if architecture guidance provided

**Contact:**
- Project: VeriPG (SystemVerilog Property Graph Generator)
- GitHub: [VeriPG Repository]
- Use Case: OpenTitan-to-RPG analysis

---

## ⏰ Timeline Request

**Ideal Timeline:**
- **Week 1-2:** Architecture review and planning
- **Week 3-4:** Immediate assertion implementation
- **Week 5-6:** Basic property support
- **Week 7-8:** Testing and refinement

**Fallback Timeline:**
- **Phase 1 Only:** Immediate assertions in 4 weeks
- **Defer Phase 2/3:** Schedule for future release

**Blocker Status:**
- 🚫 VeriPG Phase 8 blocked until basic support available
- 🚫 OpenTitan verification analysis blocked
- 🚫 Formal verification integration blocked

---

## 📋 Summary

**What We Need:** SystemVerilog Assertion parsing support in Verible

**Minimum Request:** Immediate assertions (`assert`, `assume`, `cover`)

**Full Request:** Complete SVA support (immediate + concurrent + temporal)

**Priority:** HIGH - Blocks critical VeriPG functionality

**Timeline:** 2-8 weeks depending on scope

**Impact:** Enables verification code analysis for entire SystemVerilog ecosystem

**We're Ready To Help:** Tests, validation, feedback, documentation, co-development

---

**Thank you for considering this enhancement request!** 🙏

SVA support would make Verible the first open-source SystemVerilog parser with comprehensive verification construct coverage, significantly benefiting the entire hardware design community.

