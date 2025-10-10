# Verible Enhancement Request: Expression Metadata Enrichment

**Date:** 2025-01-10  
**Requestor:** VeriPG Project Team  
**Priority:** High  
**Impact:** Semantic Graph Construction, Data Flow Analysis  

---

## Executive Summary

Request to enhance Verible's JSON CST output with **semantic metadata for expression nodes**. This will enable downstream tools (like VeriPG) to construct semantic graphs and data flow representations without complex, fragile CST traversal logic.

**Key Benefits:**
- 🎯 Reduce downstream complexity by ~70%
- 🚀 Enable efficient semantic graph construction
- 🔒 Provide stable API for data flow analysis
- 📊 Support RTL analysis tools ecosystem

---

## Problem Statement

### Current Challenge

Verible's CST provides **syntactic structure** but requires deep traversal (5-10 levels) to extract semantic information:

**Example: Simple Addition `a + b`**

Current CST (simplified):
```json
{
  "tag": "kBinaryExpression",
  "children": [
    {
      "tag": "kExpression",
      "children": [
        {
          "tag": "kReference",
          "children": [
            {
              "tag": "kLocalRoot",
              "children": [
                {
                  "tag": "kUnqualifiedId",
                  "children": [
                    {"tag": "SymbolIdentifier", "text": "a"}
                  ]
                }
              ]
            }
          ]
        }
      ]
    },
    {"tag": "+"},
    {
      "tag": "kExpression",
      "children": [
        "... (similar deep nesting for 'b')"
      ]
    }
  ]
}
```

**Issues with current structure:**
1. ❌ Requires recursive traversal to find operand identifiers
2. ❌ Operator position varies based on expression type
3. ❌ No explicit operand role information (left vs. right)
4. ❌ Type information not readily available
5. ❌ Fragile - breaks with minor CST structure changes

---

## Proposed Solution

### Add `metadata` field to expression nodes

Enhance expression-related CST nodes with a **flat, semantic metadata structure** that provides:
- Operation type (add, subtract, multiply, etc.)
- Operator symbol (+, -, *, etc.)
- Operand identifiers with roles
- Type and width information

---

## Detailed Specification

### 1. Node Types to Enhance

The following CST node types should include metadata:

| Node Type | Priority | Use Case |
|-----------|----------|----------|
| `kBinaryExpression` | **HIGH** | Arithmetic, logical, bitwise operations |
| `kTernaryExpression` | **HIGH** | Conditional expressions (mux) |
| `kUnaryExpression` | **HIGH** | Negation, bitwise NOT, reduction |
| `kFunctionCall` | Medium | Function/task calls |
| `kConcatenationExpression` | Medium | Bit concatenation |
| `kRangeSelect` | Medium | Bit slicing |
| `kBitSelect` | Medium | Single bit access |

---

### 2. Metadata Schema

#### **2.1 Binary Expression Metadata**

**Schema:**
```json
{
  "tag": "kBinaryExpression",
  "text": "a + b",
  "metadata": {
    "operation": "add",
    "operator": "+",
    "operands": [
      {
        "role": "left",
        "identifier": "a",
        "type": "reference"
      },
      {
        "role": "right",
        "identifier": "b",
        "type": "reference"
      }
    ],
    "result_type": "logic",
    "result_width": "[7:0]"
  }
}
```

**Operation Types:**
```
Arithmetic: add, subtract, multiply, divide, modulo, power
Comparison: eq, ne, lt, le, gt, ge, case_eq, case_ne
Logical: and, or
Bitwise: bit_and, bit_or, bit_xor, bit_xnor
Shift: shift_left, shift_right, shift_left_arith, shift_right_arith
```

**Operand Roles:**
- Binary: `left`, `right`

**Example 1: Addition**
```systemverilog
assign sum = a + b;
```
```json
{
  "tag": "kBinaryExpression",
  "metadata": {
    "operation": "add",
    "operator": "+",
    "operands": [
      {"role": "left", "identifier": "a", "type": "reference"},
      {"role": "right", "identifier": "b", "type": "reference"}
    ]
  }
}
```

**Example 2: Comparison**
```systemverilog
if (counter == 10)
```
```json
{
  "tag": "kBinaryExpression",
  "metadata": {
    "operation": "eq",
    "operator": "==",
    "operands": [
      {"role": "left", "identifier": "counter", "type": "reference"},
      {"role": "right", "identifier": null, "type": "literal", "value": "10"}
    ]
  }
}
```

---

#### **2.2 Ternary Expression Metadata**

**Schema:**
```json
{
  "tag": "kTernaryExpression",
  "text": "sel ? a : b",
  "metadata": {
    "operation": "ternary",
    "operator": "?:",
    "operands": [
      {
        "role": "condition",
        "identifier": "sel",
        "type": "reference"
      },
      {
        "role": "true_value",
        "identifier": "a",
        "type": "reference"
      },
      {
        "role": "false_value",
        "identifier": "b",
        "type": "reference"
      }
    ]
  }
}
```

**Operand Roles:**
- Ternary: `condition`, `true_value`, `false_value`

**Example:**
```systemverilog
assign mux_out = sel ? data_a : data_b;
```
```json
{
  "tag": "kTernaryExpression",
  "metadata": {
    "operation": "ternary",
    "operator": "?:",
    "operands": [
      {"role": "condition", "identifier": "sel", "type": "reference"},
      {"role": "true_value", "identifier": "data_a", "type": "reference"},
      {"role": "false_value", "identifier": "data_b", "type": "reference"}
    ]
  }
}
```

---

#### **2.3 Unary Expression Metadata**

**Schema:**
```json
{
  "tag": "kUnaryExpression",
  "text": "~enable",
  "metadata": {
    "operation": "bit_not",
    "operator": "~",
    "operands": [
      {
        "role": "operand",
        "identifier": "enable",
        "type": "reference"
      }
    ]
  }
}
```

**Operation Types:**
```
Bitwise: bit_not
Logical: logical_not
Arithmetic: negate, plus (unary +)
Reduction: reduce_and, reduce_or, reduce_xor, reduce_nand, reduce_nor, reduce_xnor
```

**Operand Roles:**
- Unary: `operand`

---

#### **2.4 Function Call Metadata**

**Schema:**
```json
{
  "tag": "kFunctionCall",
  "text": "calc_crc(data, poly)",
  "metadata": {
    "operation": "function_call",
    "function_name": "calc_crc",
    "operands": [
      {
        "role": "arg0",
        "identifier": "data",
        "type": "reference"
      },
      {
        "role": "arg1",
        "identifier": "poly",
        "type": "reference"
      }
    ]
  }
}
```

**Operand Roles:**
- Function call: `arg0`, `arg1`, `arg2`, ... (positional)

---

### 3. Operand Type Classification

The `"type"` field in operands should distinguish:

| Type | Description | Example |
|------|-------------|---------|
| `reference` | Variable/signal identifier | `a`, `counter`, `data_i` |
| `literal` | Constant value | `10`, `8'hFF`, `2'b01` |
| `expression` | Nested expression | Recursive metadata |

---

### 4. Nested Expressions

For nested expressions, use recursive metadata:

**Example: `(a + b) * c`**

```json
{
  "tag": "kBinaryExpression",
  "text": "(a + b) * c",
  "metadata": {
    "operation": "multiply",
    "operator": "*",
    "operands": [
      {
        "role": "left",
        "type": "expression",
        "expression_metadata": {
          "operation": "add",
          "operator": "+",
          "operands": [
            {"role": "left", "identifier": "a", "type": "reference"},
            {"role": "right", "identifier": "b", "type": "reference"}
          ]
        }
      },
      {
        "role": "right",
        "identifier": "c",
        "type": "reference"
      }
    ]
  }
}
```

---

### 5. Type and Width Information (Optional)

If type analysis is available in Verible, include:

```json
"metadata": {
  "operation": "add",
  "operator": "+",
  "operands": [...],
  "result_type": "logic",
  "result_width": "[7:0]",
  "is_signed": false
}
```

**Note:** Type inference can be added in later phases. Initial implementation should focus on operand extraction.

---

## Implementation Guidance

### Phase 1: Core Binary/Ternary/Unary (HIGH PRIORITY)

**Target nodes:**
- `kBinaryExpression`
- `kTernaryExpression`
- `kUnaryExpression`

**Required information:**
- Operation type (from operator token)
- Operator symbol (already available)
- Operand identifiers (traverse to SymbolIdentifier)
- Operand roles (based on position)

**Estimated effort:** 2-3 days

**Example implementation approach:**
```cpp
// Pseudo-code for binary expression
void EnrichBinaryExpression(CSTNode* node) {
  auto metadata = node->AddMetadata();
  
  // Extract operator
  metadata->set_operator(node->GetOperatorToken()->text());
  metadata->set_operation(MapOperatorToOperation(operator));
  
  // Extract left operand
  auto left = node->GetChild(0);
  auto left_id = ExtractIdentifier(left);
  metadata->AddOperand("left", left_id);
  
  // Extract right operand
  auto right = node->GetChild(2);
  auto right_id = ExtractIdentifier(right);
  metadata->AddOperand("right", right_id);
}

string ExtractIdentifier(CSTNode* expr) {
  // Traverse to SymbolIdentifier node
  auto symbol = FindNodeByTag(expr, "SymbolIdentifier");
  return symbol ? symbol->text() : nullptr;
}
```

---

### Phase 2: Function Calls (MEDIUM PRIORITY)

**Target nodes:**
- `kFunctionCall`

**Additional requirements:**
- Function name extraction
- Argument list parsing
- Positional argument tracking

**Estimated effort:** 1-2 days

---

### Phase 3: Complex Expressions (FUTURE)

**Target nodes:**
- `kConcatenationExpression`
- `kRangeSelect`
- `kBitSelect`
- `kReplicationExpression`

**Estimated effort:** 1-2 days each

---

## Testing Requirements

### Test Coverage

For each enhanced node type, provide tests for:

1. **Simple cases:**
   - Binary: `a + b`, `x == y`, `p & q`
   - Ternary: `sel ? a : b`
   - Unary: `~enable`, `!valid`, `&data`

2. **Nested expressions:**
   - `(a + b) * c`
   - `sel ? (a + b) : (c - d)`

3. **Edge cases:**
   - Literals as operands: `counter + 1`
   - Constants: `8'hFF & mask`
   - Complex identifiers: `pkg::constant`

### Example Test Case

**Input SystemVerilog:**
```systemverilog
module test;
  logic [7:0] a, b, c;
  assign c = a + b;
endmodule
```

**Expected JSON output (relevant section):**
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
  }
}
```

---

## Backward Compatibility

### Approach

Add metadata as **optional field**:
- Existing tools ignore unknown fields (JSON standard)
- New tools check for `metadata` field presence
- No breaking changes to existing CST structure

### Migration Path

**Version 1 (Current):**
```json
{
  "tag": "kBinaryExpression",
  "children": [...]
}
```

**Version 2 (Enhanced):**
```json
{
  "tag": "kBinaryExpression",
  "children": [...],  // Preserved
  "metadata": {...}   // NEW
}
```

Tools can:
1. Use `metadata` if present (fast path)
2. Fall back to `children` traversal (legacy path)

---

## Expected Impact

### For VeriPG

**Before enhancement:**
- ~300 lines of complex expression parsing code
- Fragile recursive tree traversal
- Manual operator/operand extraction
- Limited expression coverage

**After enhancement:**
- ~50 lines of metadata reading code
- Simple dictionary lookup
- Complete expression coverage
- Robust against CST changes

**Code reduction:** ~70%  
**Maintenance burden:** ~80% reduction

### For Other Tools

Any tool building on Verible benefits:
- Data flow analyzers
- Formal verification tools
- Code transformers
- Static analysis tools
- IDE features (refactoring, navigation)

---

## Alternative Approaches Considered

### Alternative 1: Separate Data Flow API

**Pros:** Clean separation of concerns  
**Cons:** Requires running Verible twice, memory overhead

### Alternative 2: External Post-processor

**Pros:** No Verible changes needed  
**Cons:** Duplicates parsing logic, slower, fragile

### Alternative 3: Complete Semantic Graph Export

**Pros:** Maximum information  
**Cons:** Massive scope, unclear use cases

**Decision:** Metadata enrichment provides best balance of:
- Modest implementation effort
- Maximum downstream benefit
- Preserves Verible's focus on syntax

---

## Success Criteria

1. ✅ Binary expressions have `metadata` with operation, operator, operands
2. ✅ Ternary expressions have `metadata` with all three operands properly labeled
3. ✅ Operand identifiers extracted correctly (no deep traversal needed)
4. ✅ Backward compatible (existing tools unaffected)
5. ✅ Tests cover simple, nested, and edge cases
6. ✅ Documentation updated with metadata schema

---

## References

### Related Work

- **Clang AST:** Provides semantic nodes alongside syntax tree
- **Rust syn crate:** Offers visitor pattern for semantic extraction
- **Tree-sitter:** Provides metadata hooks for language extensions

### VeriPG Use Case

VeriPG constructs a **semantic RTL property graph** for:
- Design understanding and navigation
- Connection analysis (port matching)
- Data flow tracking (dependencies)
- Behavioral modeling (FSM extraction)
- Formal verification support

**Current bottleneck:** Expression parsing accounts for 40% of extraction time and 60% of bugs.

---

## Contact & Questions

**VeriPG Project:**
- Repository: https://github.com/[your-org]/VeriPG
- Issues: VeriPG Issue #XXX

**For Verible Team:**
- Open to discuss implementation details
- Can provide additional test cases
- Happy to collaborate on design
- Can test beta versions with real RTL

---

## Appendix A: Complete Operation Mapping

### Binary Operations

| Operator | Operation Name | Category |
|----------|---------------|----------|
| `+` | `add` | Arithmetic |
| `-` | `subtract` | Arithmetic |
| `*` | `multiply` | Arithmetic |
| `/` | `divide` | Arithmetic |
| `%` | `modulo` | Arithmetic |
| `**` | `power` | Arithmetic |
| `==` | `eq` | Comparison |
| `!=` | `ne` | Comparison |
| `<` | `lt` | Comparison |
| `<=` | `le` | Comparison |
| `>` | `gt` | Comparison |
| `>=` | `ge` | Comparison |
| `===` | `case_eq` | Comparison |
| `!==` | `case_ne` | Comparison |
| `&&` | `logical_and` | Logical |
| `||` | `logical_or` | Logical |
| `&` | `bit_and` | Bitwise |
| `|` | `bit_or` | Bitwise |
| `^` | `bit_xor` | Bitwise |
| `^~` or `~^` | `bit_xnor` | Bitwise |
| `<<` | `shift_left` | Shift |
| `>>` | `shift_right` | Shift |
| `<<<` | `shift_left_arith` | Shift |
| `>>>` | `shift_right_arith` | Shift |

### Unary Operations

| Operator | Operation Name | Category |
|----------|---------------|----------|
| `~` | `bit_not` | Bitwise |
| `!` | `logical_not` | Logical |
| `-` | `negate` | Arithmetic |
| `+` | `plus` | Arithmetic |
| `&` | `reduce_and` | Reduction |
| `|` | `reduce_or` | Reduction |
| `^` | `reduce_xor` | Reduction |
| `~&` | `reduce_nand` | Reduction |
| `~|` | `reduce_nor` | Reduction |
| `^~` or `~^` | `reduce_xnor` | Reduction |

---

## Appendix B: JSON Schema

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "Verible Expression Metadata",
  "type": "object",
  "properties": {
    "metadata": {
      "type": "object",
      "required": ["operation", "operator", "operands"],
      "properties": {
        "operation": {
          "type": "string",
          "enum": ["add", "subtract", "multiply", "ternary", "bit_not", "..."]
        },
        "operator": {
          "type": "string"
        },
        "operands": {
          "type": "array",
          "items": {
            "type": "object",
            "required": ["role", "type"],
            "properties": {
              "role": {
                "type": "string",
                "enum": ["left", "right", "condition", "true_value", "false_value", "operand", "arg0", "arg1"]
              },
              "identifier": {
                "type": ["string", "null"]
              },
              "type": {
                "type": "string",
                "enum": ["reference", "literal", "expression"]
              },
              "value": {
                "type": "string"
              }
            }
          }
        },
        "result_type": {
          "type": "string"
        },
        "result_width": {
          "type": ["string", "null"]
        }
      }
    }
  }
}
```

---

**End of Specification**

*Thank you for considering this enhancement request. We believe this will significantly benefit the Verible ecosystem and enable a new class of RTL analysis tools.*

