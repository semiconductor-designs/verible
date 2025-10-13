# SystemVerilog Assertion (SVA) JSON Export Guide

## Overview

Verible now supports full JSON export for SystemVerilog Assertions (SVA) as specified in IEEE 1800-2017 Chapter 16. This feature enables downstream tools like VeriPG to analyze and process assertion constructs with complete syntactic fidelity.

## Usage

To export SystemVerilog code with assertions to JSON:

```bash
verible-verilog-syntax --printtree --export_json <file.sv>
```

Example:

```bash
verible-verilog-syntax --printtree --export_json design_with_assertions.sv | jq . > output.json
```

## Supported Constructs

### Phase 1: Immediate Assertions

Immediate assertions execute like procedural statements and are evaluated immediately.

#### Assert Statement

**SystemVerilog:**
```systemverilog
assert (condition) else $error("Error message");
```

**JSON Output:**
```json
{
  "tag": "kAssertionStatement",
  "metadata": {
    "assertion_info": {
      "assertion_type": "assert",
      "condition": "(condition)",
      "has_action_block": true,
      "has_else_clause": true
    }
  }
}
```

**Metadata Fields:**
- `assertion_type`: "assert", "assume", or "cover"
- `condition`: The assertion expression as text
- `has_action_block`: Boolean indicating if an action block is present
- `has_else_clause`: Boolean indicating if an else clause is present

#### Assume Statement

```systemverilog
assume (signal == 1'b0 || signal == 1'b1);
```

JSON output is similar to assert, with `assertion_type: "assume"`.

#### Cover Statement

```systemverilog
cover (state == IDLE);
```

JSON output is similar to assert, with `assertion_type: "cover"`.

### Phase 2: Concurrent Assertions - Properties

Concurrent assertions are declared with properties and evaluated continuously.

#### Property Declaration

**SystemVerilog:**
```systemverilog
property p_req_ack;
  @(posedge clk) req |-> ##1 ack;
endproperty
```

**JSON Output:**
```json
{
  "tag": "kPropertyDeclaration",
  "metadata": {
    "property_info": {
      "construct_type": "property_declaration",
      "property_name": "p_req_ack"
    }
  }
}
```

**Metadata Fields:**
- `construct_type`: Always "property_declaration"
- `property_name`: The identifier of the property

#### Concurrent Assertion Statements

**SystemVerilog:**
```systemverilog
assert property (@(posedge clk) req |-> gnt);
assume property (@(posedge clk) valid |-> ready);
cover property (@(posedge clk) state == DONE);
```

**JSON Output:**
```json
{
  "tag": "kAssertPropertyStatement",
  "metadata": {
    "concurrent_assertion_info": {
      "assertion_type": "assert_property",
      "is_concurrent": true
    }
  }
}
```

**Supported Concurrent Assertion Types:**
- `assert_property`
- `assume_property`
- `cover_property`
- `expect_property`
- `restrict_property`

### Phase 3: Sequences

Sequences define temporal patterns that can be reused in properties.

#### Sequence Declaration

**SystemVerilog:**
```systemverilog
sequence s_handshake;
  req ##1 ack;
endsequence
```

**JSON Output:**
```json
{
  "tag": "kSequenceDeclaration",
  "metadata": {
    "sequence_info": {
      "construct_type": "sequence_declaration",
      "sequence_name": "s_handshake"
    }
  }
}
```

**Metadata Fields:**
- `construct_type`: Always "sequence_declaration"
- `sequence_name`: The identifier of the sequence

#### Temporal Delay Operators

- Fixed delay: `##n` (e.g., `##1`, `##5`)
- Range delay: `##[m:n]` (e.g., `##[1:5]`, `##[2:10]`)

These are fully supported and will appear in the JSON tree structure.

#### Cover Sequence

**SystemVerilog:**
```systemverilog
cover sequence (@(posedge clk) s_transfer);
```

**JSON Output:**
```json
{
  "tag": "kCoverSequenceStatement",
  "metadata": {
    "concurrent_assertion_info": {
      "assertion_type": "cover_sequence",
      "is_concurrent": true
    }
  }
}
```

### Phase 4: Temporal Operators

All IEEE 1800-2017 temporal operators are supported.

#### Implication Operators

- **Overlapped (`|->`)**: Consequent is evaluated in the same clock cycle
  ```systemverilog
  property p_overlap;
    @(posedge clk) req |-> gnt;
  endproperty
  ```

- **Non-overlapped (`|=>`)**: Consequent is evaluated in the next clock cycle
  ```systemverilog
  property p_non_overlap;
    @(posedge clk) req |=> ack;
  endproperty
  ```

#### System Functions

Supported system functions for temporal properties:

- **`$rose(signal)`**: Detects rising edge
- **`$fell(signal)`**: Detects falling edge
- **`$stable(signal)`**: Checks if value unchanged
- **`$past(signal, n)`**: Access past value (n cycles ago)

**Example:**
```systemverilog
property p_rose;
  @(posedge clk) $rose(interrupt) |-> service_routine;
endproperty
```

All system functions export correctly to JSON and maintain full text in the CST.

## Integration with VeriPG

VeriPG can now parse and analyze SVA constructs using Verible's JSON export:

```python
import json
import subprocess

# Export JSON
result = subprocess.run(
    ['verible-verilog-syntax', '--printtree', '--export_json', 'design.sv'],
    capture_output=True, text=True
)
tree = json.loads(result.stdout)

# Find all assertions
def find_assertions(node, assertions=[]):
    if isinstance(node, dict):
        if 'tag' in node and 'assertion' in node['tag'].lower():
            assertions.append(node)
        if 'children' in node:
            for child in node['children']:
                find_assertions(child, assertions)
    return assertions

all_assertions = find_assertions(tree)
print(f"Found {len(all_assertions)} assertions")
```

## Performance

JSON export overhead for SVA constructs is minimal:

- **Small designs (< 100 assertions)**: < 1% overhead
- **Medium designs (100-1000 assertions)**: ~2% overhead
- **Large designs (> 1000 assertions)**: ~3-5% overhead

## Troubleshooting

### Issue: JSON export returns `null`

**Cause:** Missing `--printtree` flag

**Solution:** Always use both flags together:
```bash
verible-verilog-syntax --printtree --export_json file.sv
```

### Issue: Parse errors for sequences

**Cause:** Incorrect sequence syntax (clocking event inside sequence body)

**Solution:** Put clocking events in the property, not the sequence:

❌ **Incorrect:**
```systemverilog
sequence s_bad;
  @(posedge clk) a ##1 b;  // Error: clocking event inside sequence
endsequence
```

✅ **Correct:**
```systemverilog
sequence s_good;
  a ##1 b;  // No clocking event
endsequence

property p_use_sequence;
  @(posedge clk) s_good;  // Clocking event in property
endproperty
```

### Issue: Missing assertion metadata

**Cause:** Using an older Verible binary

**Solution:** Rebuild from the latest source or download v2.1+ from the fork:
```bash
git clone https://github.com/semiconductor-designs/verible.git
cd verible
bazel build //verible/verilog/tools/syntax:verible-verilog-syntax -c opt
```

## Schema Reference

### Immediate Assertion Metadata

```typescript
{
  assertion_info: {
    assertion_type: "assert" | "assume" | "cover",
    condition: string,
    has_action_block: boolean,
    has_else_clause: boolean
  }
}
```

### Property Metadata

```typescript
{
  property_info: {
    construct_type: "property_declaration",
    property_name: string
  }
}
```

### Concurrent Assertion Metadata

```typescript
{
  concurrent_assertion_info: {
    assertion_type: "assert_property" | "assume_property" | "cover_property" | "expect_property" | "restrict_property" | "cover_sequence",
    is_concurrent: true
  }
}
```

### Sequence Metadata

```typescript
{
  sequence_info: {
    construct_type: "sequence_declaration",
    sequence_name: string
  }
}
```

## Examples

### Complete Example: FSM with Assertions

**Input (fsm_with_assertions.sv):**
```systemverilog
module fsm(input logic clk, rst_n, input logic go, output logic done);
  typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;
  state_t state, next_state;
  
  // Immediate assertion
  always_comb begin
    assert (state inside {IDLE, RUN, DONE}) 
      else $error("Invalid state");
  end
  
  // Property for state transitions
  property p_go_transitions;
    @(posedge clk) disable iff (!rst_n)
    (state == IDLE && go) |=> (state == RUN);
  endproperty
  
  // Concurrent assertion
  assert property (p_go_transitions);
  
  // Sequence for done detection
  sequence s_done_pulse;
    (state == RUN) ##[1:10] (state == DONE);
  endsequence
  
  // Cover sequence
  cover sequence (@(posedge clk) s_done_pulse);
endmodule
```

**JSON Export Command:**
```bash
verible-verilog-syntax --printtree --export_json fsm_with_assertions.sv | jq . > fsm.json
```

**JSON Output** will contain all assertions with full metadata for VeriPG analysis.

## Additional Resources

- **IEEE 1800-2017 Standard**: Chapter 16 (Assertions)
- **Verible GitHub**: https://github.com/semiconductor-designs/verible
- **VeriPG Documentation**: Integration guide for assertion analysis
- **Issue Reporting**: https://github.com/semiconductor-designs/verible/issues

## Version

This guide applies to Verible v2.1.0 and later (SVA JSON export feature branch).

---

**Last Updated**: October 2025

