# Verible CST Node Reference

**Version:** 3.0 (with location metadata)  
**Date:** October 12, 2025  
**Audience:** VeriPG integration and SystemVerilog tool developers

---

## Overview

This document provides a comprehensive reference for Verible's Concrete Syntax Tree (CST) nodes as exported in JSON format. Each node includes:

- **Location metadata**: `start_line`, `start_column`, `end_line`, `end_column`
- **Tag**: Node type identifier (e.g., `kBinaryExpression`)
- **Text**: Original source text span
- **Metadata**: Semantic information for supported nodes
- **Children**: Sub-nodes and tokens

---

## Expression Nodes

### kBinaryExpression

**Description**: Represents binary operations (arithmetic, logical, bitwise, relational, etc.)

**Children**:
1. Left operand (Symbol)
2. Operator token (Leaf)
3. Right operand (Symbol)

**Metadata** (Added in v3.0):
```json
{
  "operation": "add|subtract|multiply|...",
  "operator": "+|-|*|...",
  "operands": [
    {"role": "left", "type": "reference|literal|expression"},
    {"role": "right", "type": "reference|literal|expression"}
  ]
}
```

**Example SystemVerilog**:
```systemverilog
assign result = a + b;
assign valid = enable && ready;
```

**JSON Structure**:
```json
{
  "tag": "kBinaryExpression",
  "location": {
    "start_line": 5,
    "start_column": 17,
    "end_line": 5,
    "end_column": 22
  },
  "text": "a + b",
  "metadata": {
    "operation": "add",
    "operator": "+",
    "operands": [
      {"role": "left", "type": "reference"},
      {"role": "right", "type": "reference"}
    ]
  },
  "children": [...]
}
```

**Operations Supported**:
- Arithmetic: `add`, `subtract`, `multiply`, `divide`, `modulo`, `power`
- Logical: `logical_and`, `logical_or`
- Bitwise: `bitwise_and`, `bitwise_or`, `bitwise_xor`, `bitwise_xnor`
- Relational: `equals`, `not_equals`, `less_than`, `less_equal`, `greater_than`, `greater_equal`
- Shifts: `shift_left`, `shift_right`, `arithmetic_shift_left`, `arithmetic_shift_right`

---

### kTernaryExpression (kConditionExpression)

**Description**: Ternary conditional operator `? :`

**Children**:
1. Condition expression
2. `?` token
3. True value expression
4. `:` token
5. False value expression

**Metadata** (Added in v3.0):
```json
{
  "operation": "ternary",
  "operands": [
    {"role": "condition", "type": "..."},
    {"role": "true_value", "type": "..."},
    {"role": "false_value", "type": "..."}
  ]
}
```

**Example SystemVerilog**:
```systemverilog
assign out = sel ? a : b;
```

---

### kUnaryPrefixExpression

**Description**: Unary prefix operators

**Children**:
1. Operator token
2. Operand expression

**Metadata** (Added in v3.0):
```json
{
  "operation": "logical_not|bitwise_not|negate|...",
  "operator": "!|~|-|...",
  "operands": [
    {"role": "operand", "type": "..."}
  ]
}
```

**Operations Supported**:
- Logical: `logical_not` (!)
- Bitwise: `bitwise_not` (~)
- Arithmetic: `negate` (-), `plus` (+)
- Reduction: `reduction_and` (&), `reduction_or` (|), `reduction_xor` (^), etc.

---

### kFunctionCall

**Description**: Function or task call

**Children**:
1. Function identifier/reference
2. Argument list (optional)

**Metadata** (Added in v3.0):
```json
{
  "operation": "function_call",
  "function_name": "get_data",
  "operands": [
    {"role": "argument", "type": "..."},
    {"role": "argument", "type": "..."}
  ]
}
```

**Example SystemVerilog**:
```systemverilog
result = get_data(addr, mode);
obj.method(arg1, arg2);
```

---

### kSystemTFCall

**Description**: System task or function call ($ prefixed)

**Metadata** (Added in v3.0):
Similar to `kFunctionCall` but for system functions like `$clog2`, `$display`, etc.

**Example SystemVerilog**:
```systemverilog
width = $clog2(DEPTH);
$display("Value: %d", data);
```

---

## Statement Nodes

### kAlwaysStatement

**Description**: Behavioral blocks (always, always_comb, always_ff, always_latch)

**Children**:
1. Block type keyword
2. Sensitivity list (optional)
3. Statement/block

**Metadata** (Added in v3.0):
```json
{
  "block_type": "always_ff|always_comb|always_latch|always",
  "sensitivity": {
    "type": "explicit|implicit|edge",
    "signals": [
      {"name": "clk", "edge": "posedge"}
    ]
  },
  "is_sequential": true,
  "is_combinational": false,
  "clock_info": {
    "signal": "clk",
    "edge": "posedge"
  },
  "reset_info": {
    "type": "async|sync",
    "signal": "rst_n",
    "active": "low"
  },
  "assignment_type": "nonblocking|blocking|mixed"
}
```

**Example SystemVerilog**:
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n)
    q <= 0;
  else
    q <= d;
end
```

---

## Coverage Nodes (Phase 9)

### kCovergroupDeclaration

**Description**: Functional coverage group declaration

**Children**:
1. `covergroup` keyword
2. Name
3. Event control (optional)
4. Coverage spec list
5. `endgroup` keyword

**Example SystemVerilog**:
```systemverilog
covergroup data_cg @(posedge clk);
  data_cp: coverpoint data_in {
    bins low = {[0:63]};
    bins high = {[64:127]};
  }
endgroup
```

---

### kCoverPoint

**Description**: Coverage point specification

**Children**:
1. Label (optional)
2. `coverpoint` keyword
3. Expression
4. Bins/options block (optional)

---

### kCoverCross

**Description**: Cross coverage of multiple coverpoints

**Children**:
1. Label (optional)
2. `cross` keyword
3. Coverpoint list
4. Cross body (optional)

**Example SystemVerilog**:
```systemverilog
cross_cov: cross addr_cp, data_cp;
```

---

### kCoverageBin

**Description**: Bins declaration within a coverpoint

**Example SystemVerilog**:
```systemverilog
bins low = {[0:63]};
illegal_bins bad = {[200:255]};
ignore_bins reserved = {101, 102};
wildcard bins read = {4'b00??};
```

---

## UDP Nodes (Phase 15)

### kUdpPrimitive

**Description**: User-Defined Primitive declaration

**Children**:
1. `primitive` keyword
2. Name
3. Port list
4. Port declarations
5. UDP body
6. `endprimitive` keyword

**Example SystemVerilog**:
```systemverilog
primitive and_gate (out, a, b);
  output out;
  input a, b;
  table
    0 0 : 0;
    0 1 : 0;
    1 0 : 0;
    1 1 : 1;
  endtable
endprimitive
```

---

### kUdpBody

**Description**: Table specification in UDP

**Children**:
1. `initial` statement (optional, for sequential)
2. `table` keyword
3. Table entries
4. `endtable` keyword

---

## Clocking Nodes (Phase 16)

### kClockingDeclaration

**Description**: Clocking block declaration

**Children**:
1. `global`/`default` qualifier (optional)
2. `clocking` keyword
3. Name (optional)
4. Event control
5. Clocking items
6. `endclocking` keyword

**Example SystemVerilog**:
```systemverilog
clocking cb @(posedge clk);
  default input #1step output #0;
  input data_in;
  output data_out;
endclocking
```

---

### kClockingItem

**Description**: Signal declaration within clocking block

**Children**:
1. Direction (input/output/inout)
2. Skew specification (optional)
3. Signal list

---

## Specify Nodes (Phase 17)

### kSpecifyBlock

**Description**: Timing specification block

**Children**:
1. `specify` keyword
2. Specify items
3. `endspecify` keyword

**Example SystemVerilog**:
```systemverilog
specify
  specparam tRise = 10, tFall = 12;
  (clk => q) = (tRise, tFall);
  $setup(data, posedge clk, 5);
  $hold(posedge clk, data, 3);
endspecify
```

---

### kSpecifyPathDeclaration

**Description**: Path delay specification

**Example SystemVerilog**:
```systemverilog
(in => out) = 10;
(clk *> q) = (5:6:7);  // min:typ:max
```

---

## Class Nodes (Phase 10)

### kClassDeclaration

**Description**: Class declaration

**Children**:
1. `virtual` qualifier (optional)
2. `class` keyword
3. Name
4. Parameter list (optional)
5. `extends` clause (optional)
6. Class items
7. `endclass` keyword

**Example SystemVerilog**:
```systemverilog
virtual class base_class #(parameter WIDTH = 8);
  pure virtual function logic [WIDTH-1:0] compute();
endclass

class derived extends base_class #(16);
  function logic [15:0] compute();
    return super.compute() + 1;
  endfunction
endclass
```

---

## Constraint Nodes (Phase 11)

### kConstraintDeclaration

**Description**: Constraint block in a class

**Children**:
1. `constraint` keyword
2. Name
3. Constraint block

**Example SystemVerilog**:
```systemverilog
class packet;
  rand logic [7:0] length;
  
  constraint length_c {
    length inside {[1:255]};
    length % 4 == 0;
  }
  
  constraint dist_c {
    length dist {0:/40, [1:254]:/20, 255:/40};
  }
endclass
```

---

## Location Metadata (All Nodes)

**Added in v3.0**: All nodes now include location metadata

```json
{
  "location": {
    "start_line": 42,
    "start_column": 10,
    "end_line": 42,
    "end_column": 25
  }
}
```

**Usage for VeriPG**:
- **Error reporting**: Point to exact source location
- **Code navigation**: Jump to definition/reference
- **Source mapping**: Map JSON back to original SystemVerilog
- **Coverage mapping**: Link coverage data to source lines

---

## Node Type Summary

| Category | Node Types | Phase | Count |
|----------|------------|-------|-------|
| **Expressions** | Binary, Unary, Ternary, Function Call, System Call | Core | 5+ |
| **Statements** | Always, If, Case, For, While, Assign | Core | 15+ |
| **Declarations** | Module, Class, Task, Function, Variable | Core | 20+ |
| **Coverage** | Covergroup, Coverpoint, Cross, Bins | Phase 9 | 4+ |
| **UDP** | Primitive, Body, Table | Phase 15 | 3+ |
| **Clocking** | Clocking Block, Items, Skew | Phase 16 | 3+ |
| **Specify** | Specify Block, Path, Timing Check | Phase 17 | 3+ |
| **Class** | Class, Method, Property | Phase 10 | 5+ |
| **Constraints** | Constraint, Rand, Solve Before | Phase 11 | 5+ |

**Total**: 60+ distinct node types with full location and metadata support

---

## VeriPG Integration Guide

### 1. Parsing SystemVerilog

```bash
verible-verilog-syntax --export_json input.sv > output.json
```

### 2. JSON Structure

```json
{
  "tag": "kDescriptionList",
  "location": { ... },
  "text": "...",
  "children": [
    {
      "tag": "kModuleDeclaration",
      "location": { ... },
      "children": [ ... ]
    }
  ]
}
```

### 3. Traversing the CST

**Python Example**:
```python
def traverse_cst(node, callback):
    if isinstance(node, dict):
        callback(node)
        if 'children' in node:
            for child in node['children']:
                if child:
                    traverse_cst(child, callback)

def find_always_blocks(cst):
    always_blocks = []
    def visitor(node):
        if node.get('tag') == 'kAlwaysStatement':
            always_blocks.append(node)
    traverse_cst(cst, visitor)
    return always_blocks
```

### 4. Using Metadata

**Extract clock info from always_ff**:
```python
always_node = find_node_by_tag(cst, 'kAlwaysStatement')
if 'metadata' in always_node:
    meta = always_node['metadata']
    if meta.get('is_sequential'):
        clock = meta['clock_info']['signal']
        edge = meta['clock_info']['edge']
        print(f"Clocked by {edge} {clock}")
```

### 5. Location Mapping

**Map to source line**:
```python
def get_source_location(node):
    loc = node.get('location', {})
    return (
        loc.get('start_line'),
        loc.get('start_column'),
        loc.get('end_line'),
        loc.get('end_column')
    )
```

---

## Version History

**v3.0 (October 2025)**:
- ✅ Added location metadata to all nodes
- ✅ Added expression metadata (binary, ternary, unary, function call)
- ✅ Added behavioral metadata (always blocks)
- ✅ Verified coverage parsing (Phase 9)
- ✅ Verified UDP support (Phase 15)
- ✅ Verified clocking support (Phase 16)
- ✅ Verified specify support (Phase 17)
- ✅ Verified class support (Phase 10)
- ✅ Verified constraint support (Phase 11)

**v2.0 (Previous)**:
- Expression metadata for binary, ternary, unary
- Behavioral metadata for always blocks
- Text field preservation

**v1.0 (Original)**:
- Basic CST export
- Tag and children structure

---

## Support & Resources

- **Verible GitHub**: https://github.com/chipsalliance/verible
- **VeriPG Fork**: https://github.com/semiconductor-designs/verible
- **Branch**: `veripg/phases-9-22-enhancements`
- **Documentation**: `/doc/`
- **Tests**: `/verible/verilog/CST/*_test.cc`, `/verible/verilog/parser/verilog-parser_test.cc`

---

## For More Information

See also:
- `JSON_METADATA_USER_GUIDE.md` - Detailed metadata usage
- `VERIPG_PHASES_9-22_PROGRESS.md` - Implementation progress
- `RELEASE_NOTES_METADATA_ENHANCEMENT.md` - Release notes

---

**This reference covers all SystemVerilog constructs supported by Verible as of October 2025, with comprehensive location and metadata support for VeriPG integration.**

