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

// Tests for local variables in SystemVerilog Assertions
// IEEE 1800-2017 Section 16.8: Local variables
// M13 Sprint 6: Variable capture and local declarations

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Single local variable in sequence
TEST(LocalVarsSVATest, SingleLocalVarInSequence) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic req, ack;\n"
      "  int data, result;\n"
      "  sequence s;\n"
      "    int v;\n"
      "    (req, v = data) ##1 (ack && (result == v));\n"
      "  endsequence\n"
      "endmodule\n", 13601);
}

// Test 2: Multiple local variables
TEST(LocalVarsSVATest, MultipleLocalVars) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic start, done;\n"
      "  int a, b, out;\n"
      "  property p;\n"
      "    int x, y;\n"
      "    (start, x=a, y=b) |-> ##[1:10] (done && (out == x+y));\n"
      "  endproperty\n"
      "endmodule\n", 13602);
}

// Test 3: Local variable in property
TEST(LocalVarsSVATest, LocalVarInProperty) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic clk, req, ack;\n"
      "  int data;\n"
      "  property p;\n"
      "    int temp;\n"
      "    @(posedge clk) (req, temp=data) |-> ##1 (ack && temp);\n"
      "  endproperty\n"
      "endmodule\n", 13603);
}

// Test 4: Local with let
TEST(LocalVarsSVATest, LocalWithLet) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic req;\n"
      "  int data, result;\n"
      "  property p;\n"
      "    let sum(a,b) = a+b;\n"
      "    int t;\n"
      "    (req, t=data) |-> ##1 (result == sum(t, 1));\n"
      "  endproperty\n"
      "endmodule\n", 13604);
}

// Test 5: Local in assertion_variable_declaration_list
TEST(LocalVarsSVATest, LocalInAssertionVarList) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic a, b, c;\n"
      "  int data;\n"
      "  property p;\n"
      "    int v1, v2;\n"
      "    let calc(x) = x * 2;\n"
      "    (a, v1=data) |-> (b, v2=v1) |-> (c && calc(v2));\n"
      "  endproperty\n"
      "endmodule\n", 13605);
}

// Test 6: Local with complex assignment
TEST(LocalVarsSVATest, LocalWithComplexAssignment) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic req, ack;\n"
      "  int a, b;\n"
      "  sequence s;\n"
      "    int x, y;\n"
      "    (req, x=a, y=b) ##1 (x > 0, y = x + 1) ##1 (ack && y);\n"
      "  endsequence\n"
      "endmodule\n", 13606);
}

// Test 7: Local variable scope test
TEST(LocalVarsSVATest, LocalVarScope) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  property p1;\n"
      "    int v;\n"
      "    (a, v=1) |-> ##1 (b && v);\n"
      "  endproperty\n"
      "  property p2;\n"
      "    int v;\n"
      "    (c, v=2) |-> ##1 (d && v);\n"
      "  endproperty\n"
      "endmodule\n", 13607);
}

// Test 8: Local with property call
TEST(LocalVarsSVATest, LocalWithPropertyCall) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic req, ack;\n"
      "  property p(int n);\n"
      "    int local;\n"
      "    (req, local=n) |-> ##1 (ack && local == n);\n"
      "  endproperty\n"
      "endmodule\n", 13608);
}

}  // namespace
}  // namespace verilog

