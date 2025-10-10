// Copyright 2017-2020 The Verible Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Tests for expression metadata in JSON export

#include "verible/verilog/CST/verilog-tree-json.h"

#include <memory>
#include <string>

#include "gtest/gtest.h"
#include "nlohmann/json.hpp"
#include "verible/common/text/symbol.h"
#include "verible/common/util/logging.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

using nlohmann::json;

// Helper function to find a node by tag in JSON tree
json FindNodeByTag(const json &node, const std::string &tag) {
  if (node.is_object() && node.contains("tag") && node["tag"] == tag) {
    return node;
  }
  if (node.is_object() && node.contains("children")) {
    for (const auto &child : node["children"]) {
      if (child.is_null()) continue;
      auto result = FindNodeByTag(child, tag);
      if (!result.is_null()) return result;
    }
  }
  return json();
}

// Helper function to parse expression and get JSON
json ParseExpressionToJson(const std::string &code) {
  const auto analyzer_ptr = std::make_unique<VerilogAnalyzer>(
      "module test; assign x = " + code + "; endmodule", "test.sv");
  const auto status = ABSL_DIE_IF_NULL(analyzer_ptr)->Analyze();
  EXPECT_TRUE(status.ok()) << status.message();
  const verible::SymbolPtr &tree_ptr = analyzer_ptr->SyntaxTree();
  EXPECT_NE(tree_ptr, nullptr);

  return ConvertVerilogTreeToJson(*tree_ptr, analyzer_ptr->Data().Contents());
}

// ============================================================================
// TDD: Binary Expression Tests (RED PHASE - These will fail initially)
// ============================================================================

TEST(VerilogTreeJsonMetadataTest, BinaryAddition) {
  // Test: Simple binary addition "a + b"
  json tree_json = ParseExpressionToJson("a + b");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null()) << "Should find kBinaryExpression node";
  
  // Check that metadata field exists
  ASSERT_TRUE(binary_expr.contains("metadata")) 
      << "Binary expression should have metadata field";
  
  const json &metadata = binary_expr["metadata"];
  
  // Check operation field
  ASSERT_TRUE(metadata.contains("operation")) 
      << "Metadata should have operation field";
  EXPECT_EQ(metadata["operation"], "add") 
      << "Operation should be 'add'";
  
  // Check operator field
  ASSERT_TRUE(metadata.contains("operator")) 
      << "Metadata should have operator field";
  EXPECT_EQ(metadata["operator"], "+") 
      << "Operator should be '+'";
  
  // Check operands array
  ASSERT_TRUE(metadata.contains("operands")) 
      << "Metadata should have operands field";
  ASSERT_TRUE(metadata["operands"].is_array()) 
      << "Operands should be an array";
  ASSERT_EQ(metadata["operands"].size(), 2) 
      << "Should have 2 operands";
  
  // Check left operand
  const json &left = metadata["operands"][0];
  EXPECT_EQ(left["role"], "left") << "First operand should have role 'left'";
  EXPECT_EQ(left["type"], "reference") << "Left operand should be a reference";
  EXPECT_EQ(left["identifier"], "a") << "Left operand identifier should be 'a'";
  
  // Check right operand
  const json &right = metadata["operands"][1];
  EXPECT_EQ(right["role"], "right") << "Second operand should have role 'right'";
  EXPECT_EQ(right["type"], "reference") << "Right operand should be a reference";
  EXPECT_EQ(right["identifier"], "b") << "Right operand identifier should be 'b'";
}

TEST(VerilogTreeJsonMetadataTest, BinarySubtraction) {
  // Test: Binary subtraction "x - y"
  json tree_json = ParseExpressionToJson("x - y");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "subtract");
  EXPECT_EQ(metadata["operator"], "-");
  EXPECT_EQ(metadata["operands"].size(), 2);
  EXPECT_EQ(metadata["operands"][0]["identifier"], "x");
  EXPECT_EQ(metadata["operands"][1]["identifier"], "y");
}

TEST(VerilogTreeJsonMetadataTest, BinaryMultiplication) {
  // Test: Binary multiplication "a * b"
  json tree_json = ParseExpressionToJson("a * b");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "multiply");
  EXPECT_EQ(metadata["operator"], "*");
}

TEST(VerilogTreeJsonMetadataTest, ComparisonEqual) {
  // Test: Equality comparison "counter == 10"
  json tree_json = ParseExpressionToJson("counter == 10");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "eq");
  EXPECT_EQ(metadata["operator"], "==");
  EXPECT_EQ(metadata["operands"].size(), 2);
  
  // Left is reference
  EXPECT_EQ(metadata["operands"][0]["type"], "reference");
  EXPECT_EQ(metadata["operands"][0]["identifier"], "counter");
  
  // Right is literal
  EXPECT_EQ(metadata["operands"][1]["type"], "literal");
}

TEST(VerilogTreeJsonMetadataTest, ComparisonNotEqual) {
  // Test: Inequality comparison "x != 0"
  json tree_json = ParseExpressionToJson("x != 0");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "ne");
  EXPECT_EQ(metadata["operator"], "!=");
}

TEST(VerilogTreeJsonMetadataTest, ComparisonLessThan) {
  // Test: Less than comparison "x < 100"
  json tree_json = ParseExpressionToJson("x < 100");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "lt");
  EXPECT_EQ(metadata["operator"], "<");
}

TEST(VerilogTreeJsonMetadataTest, LogicalAnd) {
  // Test: Logical AND "enable && valid"
  json tree_json = ParseExpressionToJson("enable && valid");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "logical_and");
  EXPECT_EQ(metadata["operator"], "&&");
}

TEST(VerilogTreeJsonMetadataTest, LogicalOr) {
  // Test: Logical OR "a || b"
  json tree_json = ParseExpressionToJson("a || b");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "logical_or");
  EXPECT_EQ(metadata["operator"], "||");
}

TEST(VerilogTreeJsonMetadataTest, BitwiseAnd) {
  // Test: Bitwise AND "flags & mask"
  json tree_json = ParseExpressionToJson("flags & mask");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "bit_and");
  EXPECT_EQ(metadata["operator"], "&");
}

TEST(VerilogTreeJsonMetadataTest, BitwiseOr) {
  // Test: Bitwise OR "a | b"
  json tree_json = ParseExpressionToJson("a | b");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "bit_or");
  EXPECT_EQ(metadata["operator"], "|");
}

TEST(VerilogTreeJsonMetadataTest, BitwiseXor) {
  // Test: Bitwise XOR "a ^ b"
  json tree_json = ParseExpressionToJson("a ^ b");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "bit_xor");
  EXPECT_EQ(metadata["operator"], "^");
}

TEST(VerilogTreeJsonMetadataTest, ShiftLeft) {
  // Test: Shift left "data << 2"
  json tree_json = ParseExpressionToJson("data << 2");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "shift_left");
  EXPECT_EQ(metadata["operator"], "<<");
}

TEST(VerilogTreeJsonMetadataTest, ShiftRight) {
  // Test: Shift right "data >> 4"
  json tree_json = ParseExpressionToJson("data >> 4");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "shift_right");
  EXPECT_EQ(metadata["operator"], ">>");
}

TEST(VerilogTreeJsonMetadataTest, AssociativeExpression) {
  // Test: Associative addition "a + b + c"
  // Verible flattens associative operators
  json tree_json = ParseExpressionToJson("a + b + c");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "add");
  EXPECT_EQ(metadata["operator"], "+");
  
  // Should have 3 operands for flattened associative expression
  ASSERT_GE(metadata["operands"].size(), 2) 
      << "Should have at least 2 operands";
  
  // First operand should be left, rest should be right or operand
  EXPECT_EQ(metadata["operands"][0]["role"], "left");
}

TEST(VerilogTreeJsonMetadataTest, NestedExpression) {
  // Test: Nested expression "(a + b) * c"
  json tree_json = ParseExpressionToJson("(a + b) * c");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  // Find the outer multiplication
  while (!binary_expr.is_null() && 
         binary_expr["metadata"]["operator"] != "*") {
    // This is the inner addition, look for sibling or parent
    tree_json = ParseExpressionToJson("(a + b) * c");
    binary_expr = tree_json; // Will need better traversal
    break;
  }

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "multiply");
  
  // Left operand should be an expression type
  const json &left = metadata["operands"][0];
  EXPECT_EQ(left["type"], "expression") 
      << "Left operand should be an expression";
  
  // Right operand should be a reference
  const json &right = metadata["operands"][1];
  EXPECT_EQ(right["type"], "reference");
  EXPECT_EQ(right["identifier"], "c");
}

TEST(VerilogTreeJsonMetadataTest, WithSizedLiteral) {
  // Test: With sized literal "data + 8'hFF"
  json tree_json = ParseExpressionToJson("data + 8'hFF");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  ASSERT_TRUE(binary_expr.contains("metadata"));
  
  const json &metadata = binary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "add");
  
  // Left is reference
  EXPECT_EQ(metadata["operands"][0]["type"], "reference");
  EXPECT_EQ(metadata["operands"][0]["identifier"], "data");
  
  // Right is literal
  EXPECT_EQ(metadata["operands"][1]["type"], "literal");
}

// ============================================================================
// Phase 2: Ternary Expression Tests
// ============================================================================

TEST(VerilogTreeJsonMetadataTest, TernarySimple) {
  // Test: Simple ternary "enable ? data : 8'h00"
  json tree_json = ParseExpressionToJson("enable ? data : 8'h00");
  json ternary_expr = FindNodeByTag(tree_json, "kConditionExpression");

  ASSERT_FALSE(ternary_expr.is_null());
  ASSERT_TRUE(ternary_expr.contains("metadata"));
  
  const json &metadata = ternary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "conditional");
  EXPECT_EQ(metadata["operator"], "?:");
  
  ASSERT_TRUE(metadata.contains("operands"));
  ASSERT_EQ(metadata["operands"].size(), 3);
  
  // Check condition
  const json &condition = metadata["operands"][0];
  EXPECT_EQ(condition["role"], "condition");
  EXPECT_EQ(condition["type"], "reference");
  EXPECT_EQ(condition["identifier"], "enable");
  
  // Check true_value
  const json &true_val = metadata["operands"][1];
  EXPECT_EQ(true_val["role"], "true_value");
  EXPECT_EQ(true_val["type"], "reference");
  EXPECT_EQ(true_val["identifier"], "data");
  
  // Check false_value
  const json &false_val = metadata["operands"][2];
  EXPECT_EQ(false_val["role"], "false_value");
  EXPECT_EQ(false_val["type"], "literal");
}

TEST(VerilogTreeJsonMetadataTest, TernaryWithExpression) {
  // Test: Ternary with expression "(x > 0) ? x : -x"
  json tree_json = ParseExpressionToJson("(x > 0) ? x : -x");
  json ternary_expr = FindNodeByTag(tree_json, "kConditionExpression");

  ASSERT_FALSE(ternary_expr.is_null());
  ASSERT_TRUE(ternary_expr.contains("metadata"));
  
  const json &metadata = ternary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "conditional");
  
  // Check condition is an expression
  const json &condition = metadata["operands"][0];
  EXPECT_EQ(condition["role"], "condition");
  EXPECT_EQ(condition["type"], "expression");
  
  // Check true_value is a reference
  const json &true_val = metadata["operands"][1];
  EXPECT_EQ(true_val["role"], "true_value");
  EXPECT_EQ(true_val["type"], "reference");
  EXPECT_EQ(true_val["identifier"], "x");
  
  // Check false_value is an expression (unary minus)
  const json &false_val = metadata["operands"][2];
  EXPECT_EQ(false_val["role"], "false_value");
  EXPECT_EQ(false_val["type"], "expression");
}

TEST(VerilogTreeJsonMetadataTest, TernaryNested) {
  // Test: Nested ternary "a ? b : (c ? d : e)"
  json tree_json = ParseExpressionToJson("a ? b : (c ? d : e)");
  json outer_ternary = FindNodeByTag(tree_json, "kConditionExpression");

  ASSERT_FALSE(outer_ternary.is_null());
  ASSERT_TRUE(outer_ternary.contains("metadata"));
  
  const json &metadata = outer_ternary["metadata"];
  EXPECT_EQ(metadata["operation"], "conditional");
  
  // Check that false_value is an expression (nested ternary)
  const json &false_val = metadata["operands"][2];
  EXPECT_EQ(false_val["role"], "false_value");
  EXPECT_EQ(false_val["type"], "expression");
}

// ============================================================================
// Phase 3: Unary Expression Tests
// ============================================================================

TEST(VerilogTreeJsonMetadataTest, UnaryLogicalNot) {
  // Test: Logical NOT "!enable"
  json tree_json = ParseExpressionToJson("!enable");
  json unary_expr = FindNodeByTag(tree_json, "kUnaryPrefixExpression");

  ASSERT_FALSE(unary_expr.is_null());
  ASSERT_TRUE(unary_expr.contains("metadata"));
  
  const json &metadata = unary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "logical_not");
  EXPECT_EQ(metadata["operator"], "!");
  
  ASSERT_TRUE(metadata.contains("operands"));
  ASSERT_EQ(metadata["operands"].size(), 1);
  
  const json &operand = metadata["operands"][0];
  EXPECT_EQ(operand["role"], "operand");
  EXPECT_EQ(operand["type"], "reference");
  EXPECT_EQ(operand["identifier"], "enable");
}

TEST(VerilogTreeJsonMetadataTest, UnaryBitwiseNot) {
  // Test: Bitwise NOT "~data"
  json tree_json = ParseExpressionToJson("~data");
  json unary_expr = FindNodeByTag(tree_json, "kUnaryPrefixExpression");

  ASSERT_FALSE(unary_expr.is_null());
  ASSERT_TRUE(unary_expr.contains("metadata"));
  
  const json &metadata = unary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "bitwise_not");
  EXPECT_EQ(metadata["operator"], "~");
  
  const json &operand = metadata["operands"][0];
  EXPECT_EQ(operand["type"], "reference");
  EXPECT_EQ(operand["identifier"], "data");
}

TEST(VerilogTreeJsonMetadataTest, UnaryMinus) {
  // Test: Unary minus "-value"
  json tree_json = ParseExpressionToJson("-value");
  json unary_expr = FindNodeByTag(tree_json, "kUnaryPrefixExpression");

  ASSERT_FALSE(unary_expr.is_null());
  ASSERT_TRUE(unary_expr.contains("metadata"));
  
  const json &metadata = unary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "negate");
  EXPECT_EQ(metadata["operator"], "-");
  
  const json &operand = metadata["operands"][0];
  EXPECT_EQ(operand["type"], "reference");
  EXPECT_EQ(operand["identifier"], "value");
}

TEST(VerilogTreeJsonMetadataTest, UnaryPlus) {
  // Test: Unary plus "+value"
  json tree_json = ParseExpressionToJson("+value");
  json unary_expr = FindNodeByTag(tree_json, "kUnaryPrefixExpression");

  ASSERT_FALSE(unary_expr.is_null());
  ASSERT_TRUE(unary_expr.contains("metadata"));
  
  const json &metadata = unary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "unary_plus");
  EXPECT_EQ(metadata["operator"], "+");
}

TEST(VerilogTreeJsonMetadataTest, UnaryReductionAnd) {
  // Test: Reduction AND "&data"
  json tree_json = ParseExpressionToJson("&data");
  json unary_expr = FindNodeByTag(tree_json, "kUnaryPrefixExpression");

  ASSERT_FALSE(unary_expr.is_null());
  ASSERT_TRUE(unary_expr.contains("metadata"));
  
  const json &metadata = unary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "reduction_and");
  EXPECT_EQ(metadata["operator"], "&");
}

TEST(VerilogTreeJsonMetadataTest, UnaryReductionOr) {
  // Test: Reduction OR "|data"
  json tree_json = ParseExpressionToJson("|data");
  json unary_expr = FindNodeByTag(tree_json, "kUnaryPrefixExpression");

  ASSERT_FALSE(unary_expr.is_null());
  ASSERT_TRUE(unary_expr.contains("metadata"));
  
  const json &metadata = unary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "reduction_or");
  EXPECT_EQ(metadata["operator"], "|");
}

TEST(VerilogTreeJsonMetadataTest, UnaryReductionXor) {
  // Test: Reduction XOR "^data"
  json tree_json = ParseExpressionToJson("^data");
  json unary_expr = FindNodeByTag(tree_json, "kUnaryPrefixExpression");

  ASSERT_FALSE(unary_expr.is_null());
  ASSERT_TRUE(unary_expr.contains("metadata"));
  
  const json &metadata = unary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "reduction_xor");
  EXPECT_EQ(metadata["operator"], "^");
}

TEST(VerilogTreeJsonMetadataTest, UnaryWithExpression) {
  // Test: Unary with expression operand "!(a > b)"
  json tree_json = ParseExpressionToJson("!(a > b)");
  json unary_expr = FindNodeByTag(tree_json, "kUnaryPrefixExpression");

  ASSERT_FALSE(unary_expr.is_null());
  ASSERT_TRUE(unary_expr.contains("metadata"));
  
  const json &metadata = unary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "logical_not");
  
  const json &operand = metadata["operands"][0];
  EXPECT_EQ(operand["role"], "operand");
  EXPECT_EQ(operand["type"], "expression");
}

TEST(VerilogTreeJsonMetadataTest, UnaryWithLiteral) {
  // Test: Unary with literal operand "-8"
  json tree_json = ParseExpressionToJson("-8");
  json unary_expr = FindNodeByTag(tree_json, "kUnaryPrefixExpression");

  ASSERT_FALSE(unary_expr.is_null());
  ASSERT_TRUE(unary_expr.contains("metadata"));
  
  const json &metadata = unary_expr["metadata"];
  EXPECT_EQ(metadata["operation"], "negate");
  
  const json &operand = metadata["operands"][0];
  EXPECT_EQ(operand["type"], "literal");
}

// ============================================================================
// Phase 4: Function Call Tests
// ============================================================================

TEST(VerilogTreeJsonMetadataTest, FunctionCallNoArgs) {
  // Test: Function call with no arguments "get_data()"
  json tree_json = ParseExpressionToJson("get_data()");
  json func_call = FindNodeByTag(tree_json, "kFunctionCall");

  ASSERT_FALSE(func_call.is_null());
  ASSERT_TRUE(func_call.contains("metadata"));
  
  const json &metadata = func_call["metadata"];
  EXPECT_EQ(metadata["operation"], "function_call");
  EXPECT_EQ(metadata["function_name"], "get_data");
  
  ASSERT_TRUE(metadata.contains("operands"));
  ASSERT_EQ(metadata["operands"].size(), 0) << "No-arg function should have 0 operands";
}

TEST(VerilogTreeJsonMetadataTest, FunctionCallSingleArg) {
  // Test: Function call with single argument "sqrt(value)"
  json tree_json = ParseExpressionToJson("sqrt(value)");
  json func_call = FindNodeByTag(tree_json, "kFunctionCall");

  ASSERT_FALSE(func_call.is_null());
  ASSERT_TRUE(func_call.contains("metadata"));
  
  const json &metadata = func_call["metadata"];
  EXPECT_EQ(metadata["operation"], "function_call");
  EXPECT_EQ(metadata["function_name"], "sqrt");
  
  ASSERT_EQ(metadata["operands"].size(), 1);
  
  const json &arg = metadata["operands"][0];
  EXPECT_EQ(arg["role"], "argument");
  EXPECT_EQ(arg["type"], "reference");
  EXPECT_EQ(arg["identifier"], "value");
}

TEST(VerilogTreeJsonMetadataTest, FunctionCallMultipleArgs) {
  // Test: Function call with multiple arguments "add(a, b, c)"
  json tree_json = ParseExpressionToJson("add(a, b, c)");
  json func_call = FindNodeByTag(tree_json, "kFunctionCall");

  ASSERT_FALSE(func_call.is_null());
  ASSERT_TRUE(func_call.contains("metadata"));
  
  const json &metadata = func_call["metadata"];
  EXPECT_EQ(metadata["operation"], "function_call");
  EXPECT_EQ(metadata["function_name"], "add");
  
  ASSERT_EQ(metadata["operands"].size(), 3);
  
  // Check all arguments
  EXPECT_EQ(metadata["operands"][0]["role"], "argument");
  EXPECT_EQ(metadata["operands"][0]["identifier"], "a");
  
  EXPECT_EQ(metadata["operands"][1]["role"], "argument");
  EXPECT_EQ(metadata["operands"][1]["identifier"], "b");
  
  EXPECT_EQ(metadata["operands"][2]["role"], "argument");
  EXPECT_EQ(metadata["operands"][2]["identifier"], "c");
}

TEST(VerilogTreeJsonMetadataTest, FunctionCallWithLiteral) {
  // Test: Function call with literal argument "max(data, 8'hFF)"
  json tree_json = ParseExpressionToJson("max(data, 8'hFF)");
  json func_call = FindNodeByTag(tree_json, "kFunctionCall");

  ASSERT_FALSE(func_call.is_null());
  ASSERT_TRUE(func_call.contains("metadata"));
  
  const json &metadata = func_call["metadata"];
  EXPECT_EQ(metadata["function_name"], "max");
  
  ASSERT_EQ(metadata["operands"].size(), 2);
  
  EXPECT_EQ(metadata["operands"][0]["type"], "reference");
  EXPECT_EQ(metadata["operands"][0]["identifier"], "data");
  
  EXPECT_EQ(metadata["operands"][1]["type"], "literal");
}

TEST(VerilogTreeJsonMetadataTest, FunctionCallWithExpression) {
  // Test: Function call with expression argument "abs(a - b)"
  json tree_json = ParseExpressionToJson("abs(a - b)");
  json func_call = FindNodeByTag(tree_json, "kFunctionCall");

  ASSERT_FALSE(func_call.is_null());
  ASSERT_TRUE(func_call.contains("metadata"));
  
  const json &metadata = func_call["metadata"];
  EXPECT_EQ(metadata["function_name"], "abs");
  
  ASSERT_EQ(metadata["operands"].size(), 1);
  
  const json &arg = metadata["operands"][0];
  EXPECT_EQ(arg["role"], "argument");
  EXPECT_EQ(arg["type"], "expression");
}

TEST(VerilogTreeJsonMetadataTest, SystemFunctionCall) {
  // Test: System function call "$clog2(WIDTH)"
  json tree_json = ParseExpressionToJson("$clog2(WIDTH)");
  
  // System functions are parsed as kSystemTFCall, not kFunctionCall
  json func_call = FindNodeByTag(tree_json, "kSystemTFCall");

  ASSERT_FALSE(func_call.is_null()) << "Should find kSystemTFCall";
  ASSERT_TRUE(func_call.contains("metadata"));
  
  const json &metadata = func_call["metadata"];
  EXPECT_EQ(metadata["operation"], "function_call");
  EXPECT_EQ(metadata["function_name"], "$clog2");
  
  ASSERT_EQ(metadata["operands"].size(), 1);
  EXPECT_EQ(metadata["operands"][0]["identifier"], "WIDTH");
}

TEST(VerilogTreeJsonMetadataTest, NestedFunctionCall) {
  // Test: Nested function call "min(max(a, b), c)"
  json tree_json = ParseExpressionToJson("min(max(a, b), c)");
  json outer_func = FindNodeByTag(tree_json, "kFunctionCall");

  ASSERT_FALSE(outer_func.is_null());
  ASSERT_TRUE(outer_func.contains("metadata"));
  
  const json &metadata = outer_func["metadata"];
  EXPECT_EQ(metadata["function_name"], "min");
  
  ASSERT_EQ(metadata["operands"].size(), 2);
  
  // First argument is an expression (nested function call)
  EXPECT_EQ(metadata["operands"][0]["type"], "expression");
  
  // Second argument is a reference
  EXPECT_EQ(metadata["operands"][1]["type"], "reference");
  EXPECT_EQ(metadata["operands"][1]["identifier"], "c");
}

// ============================================================================
// Backward Compatibility Tests
// ============================================================================

// Test that non-expression nodes don't have metadata
TEST(VerilogTreeJsonMetadataTest, NonExpressionNoMetadata) {
  const auto analyzer_ptr = std::make_unique<VerilogAnalyzer>(
      "module test; endmodule", "test.sv");
  const auto status = ABSL_DIE_IF_NULL(analyzer_ptr)->Analyze();
  EXPECT_TRUE(status.ok());
  const verible::SymbolPtr &tree_ptr = analyzer_ptr->SyntaxTree();
  EXPECT_NE(tree_ptr, nullptr);

  json tree_json = ConvertVerilogTreeToJson(
      *tree_ptr, analyzer_ptr->Data().Contents());
  
  json module_decl = FindNodeByTag(tree_json, "kModuleDeclaration");
  ASSERT_FALSE(module_decl.is_null());
  
  // Module declarations should NOT have metadata
  EXPECT_FALSE(module_decl.contains("metadata")) 
      << "Non-expression nodes should not have metadata";
}

// Test backward compatibility - text field should still exist
TEST(VerilogTreeJsonMetadataTest, BackwardCompatibilityTextField) {
  json tree_json = ParseExpressionToJson("a + b");
  json binary_expr = FindNodeByTag(tree_json, "kBinaryExpression");

  ASSERT_FALSE(binary_expr.is_null());
  
  // Should have both text (old) and metadata (new) fields
  ASSERT_TRUE(binary_expr.contains("text")) 
      << "Should maintain text field for backward compatibility";
  EXPECT_EQ(binary_expr["text"], "a + b") 
      << "Text field should contain full expression";
  
  ASSERT_TRUE(binary_expr.contains("metadata")) 
      << "Should have new metadata field";
}

}  // namespace
}  // namespace verilog

