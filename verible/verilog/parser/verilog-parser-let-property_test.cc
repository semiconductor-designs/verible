// Copyright 2025 The Verible Authors.
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

// Tests for `let` keyword in SystemVerilog Assertions (SVA) properties
// IEEE 1800-2017 Section 16.12: Let construct
// Phase 40 VeriPG support

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Basic let in property (Phase 40 example)
TEST(LetPropertyTest, BasicLetInProperty) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "property p_test;\n"
      "  let max(a, b) = (a > b) ? a : b;\n"
      "  @(posedge clk) (max(x, y) < 10);\n"
      "endproperty\n"
      "module test_let;\n"
      "  logic clk, x, y;\n"
      "  assert property (p_test);\n"
      "endmodule\n", 4001);
}

// Test 2: Let after variable declaration
TEST(LetPropertyTest, LetAfterVariable) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "property p;\n"
      "  int temp;\n"
      "  let max(a, b) = (a > b) ? a : b;\n"
      "  @(posedge clk) (max(temp, 10) < 20);\n"
      "endproperty\n"
      "module m;\n"
      "  logic clk;\n"
      "  assert property (p);\n"
      "endmodule\n", 4002);
}

// Test 3: Multiple let declarations
TEST(LetPropertyTest, MultipleLetDeclarations) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "property p;\n"
      "  let max(a, b) = (a > b) ? a : b;\n"
      "  let min(a, b) = (a < b) ? a : b;\n"
      "  @(posedge clk) (max(x, y) > min(x, y));\n"
      "endproperty\n"
      "module m;\n"
      "  logic clk, x, y;\n"
      "  assert property (p);\n"
      "endmodule\n", 4003);
}

// Test 4: Let with no parameters
TEST(LetPropertyTest, LetNoParameters) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "property p;\n"
      "  let constant = 42;\n"
      "  @(posedge clk) (data == constant);\n"
      "endproperty\n"
      "module m;\n"
      "  logic clk;\n"
      "  logic [7:0] data;\n"
      "  assert property (p);\n"
      "endmodule\n", 4004);
}

// Test 5: Let with complex expression
TEST(LetPropertyTest, LetComplexExpression) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "property p;\n"
      "  let calc(a, b, c) = (a + b) * c - (a & b);\n"
      "  @(posedge clk) (calc(x, y, z) == result);\n"
      "endproperty\n"
      "module m;\n"
      "  logic clk;\n"
      "  logic [7:0] x, y, z, result;\n"
      "  assert property (p);\n"
      "endmodule\n", 4005);
}

// Test 6: Let in sequence
TEST(LetPropertyTest, LetInSequence) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  sequence s;\n"
      "    let double(x) = x * 2;\n"
      "    a until b;\n"
      "  endsequence\n"
      "endmodule\n", 4006);
}

// Test 7: Let with variables before and after
TEST(LetPropertyTest, LetMixedWithVariables) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "property p;\n"
      "  int x;\n"
      "  let double(a) = a * 2;\n"
      "  bit flag;\n"
      "  @(posedge clk) (double(x) == 10);\n"
      "endproperty\n"
      "module m;\n"
      "  logic clk;\n"
      "  assert property (p);\n"
      "endmodule\n", 4007);
}

// Test 8: Let with multiple parameters
TEST(LetPropertyTest, LetManyParameters) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "property p;\n"
      "  let avg(a, b, c, d) = (a + b + c + d) / 4;\n"
      "  @(posedge clk) (avg(w, x, y, z) < 100);\n"
      "endproperty\n"
      "module m;\n"
      "  logic clk;\n"
      "  logic [7:0] w, x, y, z;\n"
      "  assert property (p);\n"
      "endmodule\n", 4008);
}

// Test 9: Let with logical operations
TEST(LetPropertyTest, LetLogicalOperations) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "property p;\n"
      "  let is_valid(x, y) = (x > 0) && (y < 100) && (x != y);\n"
      "  @(posedge clk) is_valid(a, b);\n"
      "endproperty\n"
      "module m;\n"
      "  logic clk;\n"
      "  int a, b;\n"
      "  assert property (p);\n"
      "endmodule\n", 4009);
}

// Test 10: Let with bit selection
TEST(LetPropertyTest, LetBitSelection) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "property p;\n"
      "  let get_msb(x) = x[7];\n"
      "  let get_lsb(x) = x[0];\n"
      "  @(posedge clk) (get_msb(data) == get_lsb(data));\n"
      "endproperty\n"
      "module m;\n"
      "  logic clk;\n"
      "  logic [7:0] data;\n"
      "  assert property (p);\n"
      "endmodule\n", 4010);
}

}  // namespace
}  // namespace verilog

