# Verible Expression Metadata Enhancement - Detailed Implementation Plan

**Date:** 2025-01-10  
**Request From:** VeriPG Project Team  
**Document Version:** 1.0  
**Status:** Planning Phase

---

## Executive Summary

This document provides a detailed implementation plan for enhancing Verible's JSON CST export with **semantic metadata for expression nodes**. The enhancement will enable downstream tools (like VeriPG) to extract operation semantics without complex CST traversal.

**Enhancement Scope:**
- Add `metadata` field to expression nodes in JSON output
- Extract operation types, operators, and operand identifiers
- Maintain backward compatibility
- No changes to CST structure itself

**Expected Implementation Time:** 10-15 days  
**Implementation Phases:** 4 phases (Core → Function Calls → Complex Expressions → Testing)

---

## 1. Current State Analysis

### 1.1 Existing Verible Architecture

#### JSON Export Entry Point
- **File:** `verible/verilog/CST/verilog-tree-json.cc`
- **Class:** `VerilogTreeToJsonConverter`
- **Key Methods:**
  - `Visit(const SyntaxTreeLeaf &)` - Handles leaf nodes (tokens)
  - `Visit(const SyntaxTreeNode &)` - Handles internal nodes (expressions, statements, etc.)

#### Recent Modification (Completed)
✅ **Text Field Addition:** All `SyntaxTreeNode` objects now include a `text` field with full source text.
- **Implementation:** Uses `verible::StringSpanOfSymbol()` to extract source text
- **Benefit:** Provides full expression text (e.g., `"a + b"`) at every node
- **Status:** Already implemented and deployed

#### Expression Helper Functions
Verible already provides helper functions in `verible/verilog/CST/expression.h`:

| Function | Purpose | Returns |
|----------|---------|---------|
| `GetUnaryPrefixOperator()` | Extract operator from unary expression | `TokenInfo*` (operator token) |
| `GetUnaryPrefixOperand()` | Extract operand from unary expression | `Symbol*` (operand subtree) |
| `GetConditionExpressionPredicate()` | Extract condition from ternary | `Symbol*` |
| `GetConditionExpressionTrueCase()` | Extract true branch from ternary | `Symbol*` |
| `GetConditionExpressionFalseCase()` | Extract false branch from ternary | `Symbol*` |
| `FindAllBinaryOperations()` | Find all binary expressions | `vector<TreeSearchMatch>` |

**Key Observation:** Helper functions exist for extracting structure, but not for extracting identifiers from operands.

#### Identifier Extraction
- **File:** `verible/verilog/CST/identifier.cc`
- **Key Function:** `AutoUnwrapIdentifier(const Symbol &)` - Extracts identifier leaf from reference
- **Usage:** Traverses through `kReference → kLocalRoot → kUnqualifiedId → SymbolIdentifier`

---

## 2. Enhancement Design

### 2.1 Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│  VerilogTreeToJsonConverter::Visit(SyntaxTreeNode)         │
│  (verible/verilog/CST/verilog-tree-json.cc)                │
└────────────────┬────────────────────────────────────────────┘
                 │
                 ├─ Already exports: "tag", "text", "children"
                 │
                 └─ NEW: Call EnrichWithMetadata(node, json)
                         │
                         └─ Check node.Tag() == NodeEnum::k...
                            │
                            ├─ kBinaryExpression → AddBinaryMetadata()
                            ├─ kUnaryPrefixExpression → AddUnaryMetadata()
                            ├─ kConditionExpression → AddTernaryMetadata()
                            ├─ kFunctionCall → AddFunctionCallMetadata()
                            └─ (future) kConcatenationExpression, etc.
```

### 2.2 Core Helper Functions to Implement

#### 2.2.1 Extract Identifier from Expression
```cpp
// New function in identifier.cc
std::string ExtractIdentifierFromExpression(const verible::Symbol &expr) {
  // Unwrap kExpression wrapper if present
  const verible::Symbol *unwrapped = UnwrapExpression(expr);
  
  // Handle kReference nodes
  if (unwrapped->Tag().tag == (int)NodeEnum::kReference) {
    const TokenInfo *simple_id = ReferenceIsSimpleIdentifier(*unwrapped);
    if (simple_id) {
      return std::string(simple_id->text());
    }
  }
  
  // Handle direct identifier leaves
  if (unwrapped->Kind() == SymbolKind::kLeaf) {
    const auto &leaf = SymbolCastToLeaf(*unwrapped);
    if (IsIdentifierLike(verilog_tokentype(leaf.Tag().tag))) {
      return std::string(leaf.get().text());
    }
  }
  
  return "";  // Complex expression or literal
}
```

#### 2.2.2 Operator to Operation Name Mapping
```cpp
// New function in verilog-tree-json.cc
std::string MapOperatorToOperation(std::string_view operator_text) {
  static const std::unordered_map<std::string_view, std::string> op_map = {
    // Arithmetic
    {"+", "add"}, {"-", "subtract"}, {"*", "multiply"}, 
    {"/", "divide"}, {"%", "modulo"}, {"**", "power"},
    
    // Comparison
    {"==", "eq"}, {"!=", "ne"}, {"<", "lt"}, {"<=", "le"},
    {">", "gt"}, {">=", "ge"}, {"===", "case_eq"}, {"!==", "case_ne"},
    
    // Logical
    {"&&", "logical_and"}, {"||", "logical_or"},
    
    // Bitwise
    {"&", "bit_and"}, {"|", "bit_or"}, {"^", "bit_xor"}, 
    {"~^", "bit_xnor"}, {"^~", "bit_xnor"},
    
    // Shift
    {"<<", "shift_left"}, {">>", "shift_right"},
    {"<<<", "shift_left_arith"}, {">>>", "shift_right_arith"},
    
    // Unary
    {"~", "bit_not"}, {"!", "logical_not"},
    
    // Ternary
    {"?", "ternary"}
  };
  
  auto it = op_map.find(operator_text);
  return it != op_map.end() ? it->second : std::string(operator_text);
}
```

#### 2.2.3 Determine Operand Type
```cpp
// New function in verilog-tree-json.cc
std::string ClassifyOperandType(const verible::Symbol &operand) {
  const verible::Symbol *unwrapped = UnwrapExpression(operand);
  
  // Check if it's a reference (variable/signal)
  if (unwrapped->Tag().tag == (int)NodeEnum::kReference) {
    return "reference";
  }
  
  // Check if it's a literal (number, string, etc.)
  if (unwrapped->Kind() == SymbolKind::kLeaf) {
    const auto &leaf = SymbolCastToLeaf(*unwrapped);
    auto token_type = verilog_tokentype(leaf.Tag().tag);
    if (token_type == TK_DecNumber || 
        token_type == TK_BinBase || 
        token_type == TK_DecBase ||
        token_type == TK_HexBase ||
        token_type == TK_OctBase ||
        token_type == TK_StringLiteral) {
      return "literal";
    }
  }
  
  // Otherwise it's a nested expression
  return "expression";
}
```

---

## 3. Implementation Plan - Phase by Phase

### Phase 1: Core Binary Expressions (HIGH PRIORITY)
**Duration:** 3-4 days  
**Files to Modify:**
- `verible/verilog/CST/verilog-tree-json.cc` (main implementation)
- `verible/verilog/CST/verilog-tree-json.h` (if adding new class methods)
- `verible/verilog/CST/identifier.cc` (helper functions)
- `verible/verilog/CST/identifier.h` (function declarations)

#### 3.1.1 Implementation Steps

**Step 1: Add Helper Functions**
Location: `verible/verilog/CST/identifier.cc`

```cpp
// Add to identifier.cc
std::string ExtractIdentifierFromExpression(const verible::Symbol &expr) {
  // Implementation as shown in section 2.2.1
}

// Add to identifier.h
std::string ExtractIdentifierFromExpression(const verible::Symbol &);
```

**Step 2: Add Metadata Generation for Binary Expressions**
Location: `verible/verilog/CST/verilog-tree-json.cc`

```cpp
// Add new method to VerilogTreeToJsonConverter class
void AddBinaryExpressionMetadata(const verible::SyntaxTreeNode &node, json &value) {
  // Binary expression structure:
  // node[0] = left operand
  // node[1] = operator (can be multiple for associative operators)
  // node[2] = right operand (for simple binary)
  // node[2,4,6...] = additional operands for flattened associative expressions
  
  json metadata = json::object();
  
  // Extract operator (node[1])
  if (node.size() < 3) return;  // Invalid structure
  
  const auto *op_symbol = node[1].get();
  if (!op_symbol || op_symbol->Kind() != verible::SymbolKind::kLeaf) return;
  
  const auto &op_leaf = verible::SymbolCastToLeaf(*op_symbol);
  std::string_view operator_text = op_leaf.get().text();
  
  metadata["operation"] = MapOperatorToOperation(operator_text);
  metadata["operator"] = std::string(operator_text);
  
  // Extract operands
  json operands = json::array();
  
  // For associative operators (a+b+c), we have multiple operands
  // node[0] = first operand
  // node[2] = second operand
  // node[4] = third operand (if exists)
  // etc.
  
  // Left operand
  if (node[0]) {
    json left_operand = json::object();
    left_operand["role"] = "left";
    left_operand["type"] = ClassifyOperandType(*node[0]);
    
    std::string identifier = ExtractIdentifierFromExpression(*node[0]);
    if (!identifier.empty()) {
      left_operand["identifier"] = identifier;
    } else {
      // Nested expression - use the text field
      left_operand["identifier"] = nullptr;
      left_operand["expression_text"] = std::string(verible::StringSpanOfSymbol(*node[0]));
    }
    operands.push_back(left_operand);
  }
  
  // Right operand(s)
  for (size_t i = 2; i < node.size(); i += 2) {
    if (node[i]) {
      json right_operand = json::object();
      right_operand["role"] = i == 2 ? "right" : "operand";  // First right, then generic
      right_operand["type"] = ClassifyOperandType(*node[i]);
      
      std::string identifier = ExtractIdentifierFromExpression(*node[i]);
      if (!identifier.empty()) {
        right_operand["identifier"] = identifier;
      } else {
        right_operand["identifier"] = nullptr;
        right_operand["expression_text"] = std::string(verible::StringSpanOfSymbol(*node[i]));
      }
      operands.push_back(right_operand);
    }
  }
  
  metadata["operands"] = operands;
  value["metadata"] = metadata;
}
```

**Step 3: Integrate into Visit() Method**
```cpp
// Modify VerilogTreeToJsonConverter::Visit(const SyntaxTreeNode &node)
void VerilogTreeToJsonConverter::Visit(const verible::SyntaxTreeNode &node) {
  *value_ = json::object();
  (*value_)["tag"] = NodeEnumToString(static_cast<NodeEnum>(node.Tag().tag));
  
  // Extract and include the full source text for this node
  std::string_view node_text = verible::StringSpanOfSymbol(node);
  if (!node_text.empty()) {
    (*value_)["text"] = std::string(node_text);
  }
  
  // NEW: Add metadata for supported expression types
  NodeEnum tag = static_cast<NodeEnum>(node.Tag().tag);
  if (tag == NodeEnum::kBinaryExpression) {
    AddBinaryExpressionMetadata(node, *value_);
  }
  
  json &children = (*value_)["children"] = json::array();
  
  {
    const verible::ValueSaver<json *> value_saver(&value_, nullptr);
    for (const auto &child : node.children()) {
      value_ = &children.emplace_back(nullptr);
      if (child) child->Accept(this);
    }
  }
}
```

#### 3.1.2 Test Cases for Phase 1

Create test file: `verible/verilog/CST/verilog-tree-json-metadata_test.cc`

```cpp
TEST(VerilogTreeJsonMetadataTest, SimpleBinaryAddition) {
  // Input: assign c = a + b;
  // Expected metadata:
  // {
  //   "operation": "add",
  //   "operator": "+",
  //   "operands": [
  //     {"role": "left", "identifier": "a", "type": "reference"},
  //     {"role": "right", "identifier": "b", "type": "reference"}
  //   ]
  // }
}

TEST(VerilogTreeJsonMetadataTest, BinaryWithLiteral) {
  // Input: assign c = counter + 1;
  // Expected: right operand type = "literal"
}

TEST(VerilogTreeJsonMetadataTest, AssociativeExpression) {
  // Input: assign d = a + b + c;
  // Expected: 3 operands
}

TEST(VerilogTreeJsonMetadataTest, NestedExpression) {
  // Input: assign d = (a + b) * c;
  // Expected: left operand type = "expression"
}

TEST(VerilogTreeJsonMetadataTest, ComparisonOperator) {
  // Input: if (counter == 10)
  // Expected: operation = "eq", operator = "=="
}
```

---

### Phase 2: Unary & Ternary Expressions (HIGH PRIORITY)
**Duration:** 2-3 days  
**Dependencies:** Phase 1 complete

#### 3.2.1 Unary Expressions

```cpp
void AddUnaryExpressionMetadata(const verible::SyntaxTreeNode &node, json &value) {
  // Unary expression structure:
  // node[0] = operator
  // node[1] = operand
  
  if (node.size() < 2) return;
  
  json metadata = json::object();
  
  // Extract operator
  const auto *op_symbol = node[0].get();
  if (!op_symbol || op_symbol->Kind() != verible::SymbolKind::kLeaf) return;
  
  const auto &op_leaf = verible::SymbolCastToLeaf(*op_symbol);
  std::string_view operator_text = op_leaf.get().text();
  
  metadata["operation"] = MapOperatorToOperation(operator_text);
  metadata["operator"] = std::string(operator_text);
  
  // Extract operand
  json operands = json::array();
  if (node[1]) {
    json operand = json::object();
    operand["role"] = "operand";
    operand["type"] = ClassifyOperandType(*node[1]);
    
    std::string identifier = ExtractIdentifierFromExpression(*node[1]);
    if (!identifier.empty()) {
      operand["identifier"] = identifier;
    } else {
      operand["identifier"] = nullptr;
      operand["expression_text"] = std::string(verible::StringSpanOfSymbol(*node[1]));
    }
    operands.push_back(operand);
  }
  
  metadata["operands"] = operands;
  value["metadata"] = metadata;
}
```

#### 3.2.2 Ternary (Condition) Expressions

```cpp
void AddTernaryExpressionMetadata(const verible::SyntaxTreeNode &node, json &value) {
  // Ternary expression structure (kConditionExpression):
  // node[0] = condition
  // node[1] = '?'
  // node[2] = true_case
  // node[3] = ':'
  // node[4] = false_case
  
  if (node.size() < 5) return;
  
  json metadata = json::object();
  metadata["operation"] = "ternary";
  metadata["operator"] = "?:";
  
  json operands = json::array();
  
  // Condition
  if (node[0]) {
    json condition = json::object();
    condition["role"] = "condition";
    condition["type"] = ClassifyOperandType(*node[0]);
    
    std::string identifier = ExtractIdentifierFromExpression(*node[0]);
    if (!identifier.empty()) {
      condition["identifier"] = identifier;
    } else {
      condition["identifier"] = nullptr;
      condition["expression_text"] = std::string(verible::StringSpanOfSymbol(*node[0]));
    }
    operands.push_back(condition);
  }
  
  // True case
  if (node[2]) {
    json true_case = json::object();
    true_case["role"] = "true_value";
    true_case["type"] = ClassifyOperandType(*node[2]);
    
    std::string identifier = ExtractIdentifierFromExpression(*node[2]);
    if (!identifier.empty()) {
      true_case["identifier"] = identifier;
    } else {
      true_case["identifier"] = nullptr;
      true_case["expression_text"] = std::string(verible::StringSpanOfSymbol(*node[2]));
    }
    operands.push_back(true_case);
  }
  
  // False case
  if (node[4]) {
    json false_case = json::object();
    false_case["role"] = "false_value";
    false_case["type"] = ClassifyOperandType(*node[4]);
    
    std::string identifier = ExtractIdentifierFromExpression(*node[4]);
    if (!identifier.empty()) {
      false_case["identifier"] = identifier;
    } else {
      false_case["identifier"] = nullptr;
      false_case["expression_text"] = std::string(verible::StringSpanOfSymbol(*node[4]));
    }
    operands.push_back(false_case);
  }
  
  metadata["operands"] = operands;
  value["metadata"] = metadata;
}
```

#### 3.2.3 Integration

```cpp
// Update Visit() method
void VerilogTreeToJsonConverter::Visit(const verible::SyntaxTreeNode &node) {
  *value_ = json::object();
  (*value_)["tag"] = NodeEnumToString(static_cast<NodeEnum>(node.Tag().tag));
  
  std::string_view node_text = verible::StringSpanOfSymbol(node);
  if (!node_text.empty()) {
    (*value_)["text"] = std::string(node_text);
  }
  
  // Add metadata for supported expression types
  NodeEnum tag = static_cast<NodeEnum>(node.Tag().tag);
  if (tag == NodeEnum::kBinaryExpression) {
    AddBinaryExpressionMetadata(node, *value_);
  } else if (tag == NodeEnum::kUnaryPrefixExpression) {
    AddUnaryExpressionMetadata(node, *value_);
  } else if (tag == NodeEnum::kConditionExpression) {
    AddTernaryExpressionMetadata(node, *value_);
  }
  
  json &children = (*value_)["children"] = json::array();
  
  {
    const verible::ValueSaver<json *> value_saver(&value_, nullptr);
    for (const auto &child : node.children()) {
      value_ = &children.emplace_back(nullptr);
      if (child) child->Accept(this);
    }
  }
}
```

#### 3.2.4 Test Cases for Phase 2

```cpp
TEST(VerilogTreeJsonMetadataTest, UnaryBitwiseNot) {
  // Input: assign y = ~enable;
  // Expected: operation = "bit_not", operator = "~", operand role = "operand"
}

TEST(VerilogTreeJsonMetadataTest, UnaryLogicalNot) {
  // Input: assign y = !valid;
  // Expected: operation = "logical_not", operator = "!"
}

TEST(VerilogTreeJsonMetadataTest, TernaryMux) {
  // Input: assign out = sel ? a : b;
  // Expected: operation = "ternary", 3 operands with roles
}

TEST(VerilogTreeJsonMetadataTest, NestedTernary) {
  // Input: assign out = sel ? (ena ? a : b) : c;
  // Expected: true_value type = "expression"
}
```

---

### Phase 3: Function Calls (MEDIUM PRIORITY)
**Duration:** 2-3 days  
**Dependencies:** Phase 1 & 2 complete

#### 3.3.1 Function Call Implementation

```cpp
void AddFunctionCallMetadata(const verible::SyntaxTreeNode &node, json &value) {
  // Function call structure (kFunctionCall):
  // node[0] = kReferenceCallBase
  //   node[0][0] = kReference (function name)
  //   node[0][1] = kParenGroup (arguments)
  
  json metadata = json::object();
  metadata["operation"] = "function_call";
  
  // Extract function name
  const auto *function_name_leaf = GetFunctionCallName(node);
  if (function_name_leaf) {
    metadata["function_name"] = std::string(function_name_leaf->get().text());
  }
  
  // Extract arguments from kParenGroup
  // This requires traversing the argument list
  const auto *reference_call_base = GetSubtreeAsNode(node, NodeEnum::kFunctionCall, 0);
  if (reference_call_base) {
    const auto *paren_group = GetSubtreeAsNode(*reference_call_base, 
                                               NodeEnum::kReferenceCallBase, 1);
    if (paren_group && paren_group->MatchesTag(NodeEnum::kParenGroup)) {
      json operands = json::array();
      
      // Arguments are in kActualParameterList or kActualParameterPositionalList
      // Traverse and extract each argument
      int arg_index = 0;
      for (const auto &child : paren_group->children()) {
        if (child && child->Kind() == verible::SymbolKind::kNode) {
          const auto &arg_node = verible::SymbolCastToNode(*child);
          // Extract argument identifier
          json arg = json::object();
          arg["role"] = "arg" + std::to_string(arg_index);
          arg["type"] = ClassifyOperandType(arg_node);
          
          std::string identifier = ExtractIdentifierFromExpression(arg_node);
          if (!identifier.empty()) {
            arg["identifier"] = identifier;
          } else {
            arg["identifier"] = nullptr;
            arg["expression_text"] = std::string(verible::StringSpanOfSymbol(arg_node));
          }
          operands.push_back(arg);
          arg_index++;
        }
      }
      
      metadata["operands"] = operands;
    }
  }
  
  value["metadata"] = metadata;
}
```

---

### Phase 4: Comprehensive Testing & Integration
**Duration:** 3-4 days  
**Dependencies:** Phases 1, 2, 3 complete

#### 3.4.1 Integration Testing

Create comprehensive test file: `test_metadata_integration.sv`

```systemverilog
module test_metadata_integration;
  logic [7:0] a, b, c, d;
  logic sel, enable, valid;
  logic [7:0] counter;
  logic [7:0] result;
  
  // Binary expressions
  assign c = a + b;                    // Simple addition
  assign c = a - b;                    // Subtraction
  assign c = a * b;                    // Multiplication
  assign c = a & b;                    // Bitwise AND
  assign c = a | b;                    // Bitwise OR
  assign c = a ^ b;                    // Bitwise XOR
  assign d = a + b + c;                // Associative (3 operands)
  assign d = (a + b) * c;              // Nested expression
  assign result = counter + 1;         // With literal
  assign result = counter + 8'hFF;     // With sized literal
  
  // Comparison
  assign valid = (counter == 10);      // Equality
  assign valid = (counter != 0);       // Inequality
  assign valid = (counter < 100);      // Less than
  assign valid = (counter >= 50);      // Greater than or equal
  
  // Logical
  assign valid = enable && !sel;       // Logical AND with NOT
  assign valid = (a > b) || (c < d);   // Logical OR with comparisons
  
  // Unary expressions
  assign result = ~enable;             // Bitwise NOT
  assign valid = !enable;              // Logical NOT
  assign result = -counter;            // Negation
  assign valid = &data_bus;            // Reduction AND
  assign valid = |data_bus;            // Reduction OR
  assign valid = ^data_bus;            // Reduction XOR
  
  // Ternary expressions
  assign result = sel ? a : b;         // Simple mux
  assign result = sel ? (a + b) : c;   // With nested expression
  assign result = enable ? (sel ? a : b) : c;  // Nested ternary
  
  // Function calls (if supported)
  assign result = $clog2(counter);
  assign result = my_func(a, b);
  assign result = pkg::calc_crc(data, poly);
  
  // Complex expressions
  assign result = (a + b) * (c - d);   // Multiple nested
  assign result = sel ? (a & b) : (c | d);  // Ternary with operations
  assign valid = ((counter > 10) && enable) || reset;  // Complex logical
  
endmodule
```

#### 3.4.2 Validation Script

Create Python validation script: `validate_metadata.py`

```python
#!/usr/bin/env python3
"""Validate that metadata is correctly generated for all expression types."""

import json
import subprocess
import sys

def run_verible_json(sv_file):
    """Run verible-verilog-syntax with JSON export."""
    result = subprocess.run(
        ['verible-verilog-syntax', '--export_json', sv_file],
        capture_output=True,
        text=True
    )
    return json.loads(result.stdout)

def find_nodes_by_tag(node, tag):
    """Recursively find all nodes with the given tag."""
    results = []
    if isinstance(node, dict):
        if node.get('tag') == tag:
            results.append(node)
        for child in node.get('children', []):
            if child is not None:
                results.extend(find_nodes_by_tag(child, tag))
    return results

def validate_binary_expression(node):
    """Validate binary expression metadata."""
    assert 'metadata' in node, "Binary expression missing metadata"
    metadata = node['metadata']
    
    assert 'operation' in metadata, "Missing operation field"
    assert 'operator' in metadata, "Missing operator field"
    assert 'operands' in metadata, "Missing operands field"
    
    operands = metadata['operands']
    assert len(operands) >= 2, f"Expected at least 2 operands, got {len(operands)}"
    
    # Validate first operand has 'left' role
    assert operands[0]['role'] == 'left', "First operand should have 'left' role"
    
    # Validate second operand has 'right' role
    assert operands[1]['role'] == 'right', "Second operand should have 'right' role"
    
    # All operands should have 'type' field
    for op in operands:
        assert 'type' in op, "Operand missing type field"
        assert op['type'] in ['reference', 'literal', 'expression'], \
            f"Invalid operand type: {op['type']}"

def validate_unary_expression(node):
    """Validate unary expression metadata."""
    assert 'metadata' in node, "Unary expression missing metadata"
    metadata = node['metadata']
    
    assert 'operation' in metadata, "Missing operation field"
    assert 'operator' in metadata, "Missing operator field"
    assert 'operands' in metadata, "Missing operands field"
    
    operands = metadata['operands']
    assert len(operands) == 1, f"Expected 1 operand, got {len(operands)}"
    assert operands[0]['role'] == 'operand', "Operand should have 'operand' role"

def validate_ternary_expression(node):
    """Validate ternary expression metadata."""
    assert 'metadata' in node, "Ternary expression missing metadata"
    metadata = node['metadata']
    
    assert 'operation' in metadata, "Missing operation field"
    assert metadata['operation'] == 'ternary', "Operation should be 'ternary'"
    assert 'operator' in metadata, "Missing operator field"
    assert metadata['operator'] == '?:', "Operator should be '?:'"
    assert 'operands' in metadata, "Missing operands field"
    
    operands = metadata['operands']
    assert len(operands) == 3, f"Expected 3 operands, got {len(operands)}"
    
    roles = [op['role'] for op in operands]
    assert 'condition' in roles, "Missing 'condition' role"
    assert 'true_value' in roles, "Missing 'true_value' role"
    assert 'false_value' in roles, "Missing 'false_value' role"

def main():
    json_tree = run_verible_json('test_metadata_integration.sv')
    
    # Find and validate all expression types
    binary_exprs = find_nodes_by_tag(json_tree, 'kBinaryExpression')
    unary_exprs = find_nodes_by_tag(json_tree, 'kUnaryPrefixExpression')
    ternary_exprs = find_nodes_by_tag(json_tree, 'kConditionExpression')
    
    print(f"Found {len(binary_exprs)} binary expressions")
    print(f"Found {len(unary_exprs)} unary expressions")
    print(f"Found {len(ternary_exprs)} ternary expressions")
    
    for expr in binary_exprs:
        validate_binary_expression(expr)
    
    for expr in unary_exprs:
        validate_unary_expression(expr)
    
    for expr in ternary_exprs:
        validate_ternary_expression(expr)
    
    print("✓ All validations passed!")

if __name__ == '__main__':
    main()
```

---

## 4. Build System Changes

### 4.1 Files Requiring Build Updates

#### 4.1.1 Add Test Target to BUILD File

**File:** `verible/verilog/CST/BUILD`

```python
cc_test(
    name = "verilog-tree-json-metadata_test",
    srcs = ["verilog-tree-json-metadata_test.cc"],
    deps = [
        ":expression",
        ":identifier",
        ":verilog-tree-json",
        "//verible/common/text:concrete-syntax-tree",
        "//verible/common/text:symbol",
        "//verible/common/text:tree-utils",
        "//verible/verilog/analysis:verilog-analyzer",
        "//verible/verilog/parser:verilog-parser",
        "@com_google_googletest//:gtest_main",
        "@nlohmann_json//:singleheader-json",
    ],
)
```

#### 4.1.2 Update Dependencies (if adding new files)

If creating new helper files, update `deps` in the `verilog-tree-json` target:

```python
cc_library(
    name = "verilog-tree-json",
    srcs = ["verilog-tree-json.cc"],
    hdrs = ["verilog-tree-json.h"],
    deps = [
        ":identifier",  # For ExtractIdentifierFromExpression
        ":verilog-nonterminals",
        "//verible/common/text:concrete-syntax-leaf",
        "//verible/common/text:concrete-syntax-tree",
        "//verible/common/text:symbol",
        "//verible/common/text:token-info",
        "//verible/common/text:token-info-json",
        "//verible/common/text:tree-utils",
        "//verible/common/text:visitors",
        "//verible/common/util:value-saver",
        "//verible/verilog/parser:verilog-token",
        "//verible/verilog/parser:verilog-token-classifications",
        "//verible/verilog/parser:verilog-token-enum",
        "@nlohmann_json//:singleheader-json",
    ],
)
```

---

## 5. Testing Strategy

### 5.1 Unit Tests (Per Phase)

| Phase | Test File | Test Count | Coverage |
|-------|-----------|------------|----------|
| Phase 1 | `verilog-tree-json-metadata_test.cc` | 10-15 tests | All binary operators |
| Phase 2 | Same file | +10 tests | Unary + Ternary |
| Phase 3 | Same file | +5 tests | Function calls |
| Phase 4 | Integration test | 1 comprehensive | Real-world code |

### 5.2 Integration Tests

- **Test File:** `test_metadata_integration.sv` (as shown in section 3.4.1)
- **Validation:** Python script checks all metadata fields
- **Coverage:** All expression types in realistic combinations

### 5.3 Regression Tests

- Run existing Verible test suite: `bazel test //verible/verilog/...`
- Ensure no breaking changes to existing JSON structure
- Verify backward compatibility (tools ignoring new fields still work)

### 5.4 VeriPG Integration Test

- Copy enhanced Verible binary to VeriPG
- Run VeriPG test suite: `pytest tests/`
- Verify parameter extraction works correctly
- Measure complexity reduction in VeriPG code

---

## 6. Documentation Updates

### 6.1 Files to Update

1. **Verible README:** Document new `metadata` field in JSON export
   - File: `README.md`
   - Section: "JSON Export Format"

2. **JSON Export Documentation:** Add metadata schema
   - File: `doc/verible_json_format.md` (create if doesn't exist)
   - Include: Schema definition, examples, field descriptions

3. **Release Notes:** Add to next release
   - Enhancement: "Added semantic metadata to expression nodes in JSON export"
   - Breaking Changes: None (backward compatible)

### 6.2 Example Documentation Entry

```markdown
## JSON Export Metadata (v0.0-XXXX+)

Starting from version v0.0-XXXX, Verible's JSON export includes an optional
`metadata` field for expression nodes. This field provides semantic information
about operations, operators, and operands without requiring deep CST traversal.

### Supported Node Types

- `kBinaryExpression`: Binary operations (arithmetic, logical, bitwise, comparison, shift)
- `kUnaryPrefixExpression`: Unary operations (negation, bitwise NOT, logical NOT, reduction)
- `kConditionExpression`: Ternary conditional expressions (`? :`)
- `kFunctionCall`: Function and task calls (optional)

### Metadata Schema

#### Binary Expression Example

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
    ]
  },
  "children": [...]
}
```

### Operand Types

- `reference`: Variable or signal identifier
- `literal`: Constant value (number, string)
- `expression`: Nested expression (identifier will be null, use text field)

### Backward Compatibility

The `metadata` field is optional. Existing tools that don't expect this field
will ignore it automatically (standard JSON behavior). The `children` array
is always present and unchanged.
```

---

## 7. Risk Assessment

### 7.1 Technical Risks

| Risk | Severity | Mitigation |
|------|----------|------------|
| Performance impact on large files | Medium | Profile JSON generation; optimize if >5% slowdown |
| Complex expression edge cases | Medium | Comprehensive test suite; iterative refinement |
| Identifier extraction failures | Low | Fallback to `null` identifier, include `text` field |
| Build system issues | Low | Minimal dependency changes; test on CI |

### 7.2 Integration Risks

| Risk | Severity | Mitigation |
|------|----------|------------|
| Breaking VeriPG compatibility | Low | VeriPG already uses `text` field fallback |
| Upstream contribution conflicts | Medium | Keep changes isolated; document thoroughly |
| Maintenance burden | Low | Well-tested, localized changes |

---

## 8. Success Criteria

### 8.1 Phase Completion Criteria

**Phase 1 Complete:**
- ✅ Binary expressions have metadata with operation, operator, operands
- ✅ All unit tests pass (10+ tests)
- ✅ Integration test validates simple binary operations

**Phase 2 Complete:**
- ✅ Unary and ternary expressions have metadata
- ✅ All unit tests pass (20+ tests total)
- ✅ Integration test validates all three expression types

**Phase 3 Complete:**
- ✅ Function calls have metadata (optional)
- ✅ All unit tests pass (25+ tests total)

**Phase 4 Complete:**
- ✅ Comprehensive integration test passes
- ✅ No regressions in existing Verible tests
- ✅ VeriPG integration test passes
- ✅ Documentation updated

### 8.2 VeriPG Integration Success

- ✅ VeriPG parameter extraction test passes with metadata
- ✅ VeriPG expression parsing code reduced by ~70%
- ✅ VeriPG performance improves (faster parsing)

---

## 9. Timeline

| Phase | Duration | Start | End | Deliverable |
|-------|----------|-------|-----|-------------|
| Phase 1: Binary Expressions | 3-4 days | Day 1 | Day 4 | Binary metadata working |
| Phase 2: Unary & Ternary | 2-3 days | Day 5 | Day 7 | All core expressions working |
| Phase 3: Function Calls | 2-3 days | Day 8 | Day 10 | Function call metadata (optional) |
| Phase 4: Testing & Integration | 3-4 days | Day 11 | Day 15 | Full test suite, documentation |
| **Total** | **10-15 days** | **Day 1** | **Day 15** | **Production-ready enhancement** |

---

## 10. Rollout Plan

### 10.1 Development Workflow

1. **Branch Creation:** Create feature branch `feature/expression-metadata`
2. **Phase-by-Phase Development:** Complete each phase sequentially
3. **Local Testing:** Run unit tests after each phase
4. **Integration Testing:** Test with VeriPG after Phase 2
5. **Code Review:** Internal review before merge
6. **Merge to Fork:** Merge to `semiconductor-designs/verible`
7. **VeriPG Deployment:** Update VeriPG to use new binary
8. **Upstream Contribution (Optional):** Submit PR to `chipsalliance/verible`

### 10.2 VeriPG Integration Steps

1. Build enhanced Verible: `bazel build --config=verible-verilog-syntax --macos_minimum_os=10.15`
2. Copy binary to VeriPG: `cp bazel-bin/.../verible-verilog-syntax VeriPG/tools/verible/bin/`
3. Update VeriPG code to use metadata (reduce expression parsing complexity)
4. Run VeriPG tests: `pytest tests/`
5. Performance benchmark: Compare before/after parsing speed

---

## 11. Open Questions & Future Enhancements

### 11.1 Open Questions

1. **Type Information:** Should we include result type and width? (Requires type inference)
2. **Complex Expressions:** Concatenation `{}`, bit slicing `[7:0]` - Phase 5?
3. **Nested Expression Representation:** Recursive metadata vs. text field?
4. **Performance:** What's the acceptable overhead for metadata generation?

### 11.2 Future Enhancements (Post-Initial Implementation)

1. **Type Inference:** Add `result_type`, `result_width`, `is_signed` fields
2. **Complex Expressions:** Support concatenation, bit selection, replication
3. **System Function Calls:** Special handling for `$clog2`, `$bits`, etc.
4. **Macro Expansions:** Include metadata for macro-generated expressions
5. **Source Location:** Add line/column information for each operand

---

## 12. References

### 12.1 Verible Codebase

- `verible/verilog/CST/verilog-tree-json.cc` - JSON export entry point
- `verible/verilog/CST/expression.h` - Expression helper functions
- `verible/verilog/CST/identifier.cc` - Identifier extraction utilities
- `verible/verilog/CST/verilog-nonterminals.h` - NodeEnum definitions

### 12.2 Related Documentation

- VeriPG Enhancement Request: `doc/VERIBLE_ENHANCEMENT_REQUEST.md`
- Previous Modification Brief: `doc/VERIBLE_MODIFICATION_BRIEF.md`
- Verible JSON Export: `doc/indexing.md` (existing documentation)

### 12.3 External References

- JSON Schema Specification: https://json-schema.org/
- nlohmann/json Library: https://github.com/nlohmann/json
- SystemVerilog Operators: IEEE 1800-2017 Section 11

---

**Document End**

*This plan is a living document and will be updated as implementation progresses.*

