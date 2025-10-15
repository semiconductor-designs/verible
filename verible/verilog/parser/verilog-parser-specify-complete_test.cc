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

// Tests for complete specify block features in SystemVerilog
// IEEE 1800-2017 Chapter 31: Specify blocks
// M14 Week 3: Verify complete specify implementation

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Basic specify block (verify existing)
TEST(SpecifyCompleteTest, BasicSpecifyBlock) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = 1.5;\n"
      "  endspecify\n"
      "endmodule\n", 14201);
}

// Test 2: showcancelled path
TEST(SpecifyCompleteTest, ShowcancelledPath) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input a, output b);\n"
      "  specify\n"
      "    showcancelled (a => b) = 1.5;\n"
      "  endspecify\n"
      "endmodule\n", 14202);
}

// Test 3: noshowcancelled path
TEST(SpecifyCompleteTest, NoshowcancelledPath) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input a, output b);\n"
      "  specify\n"
      "    noshowcancelled (a => b) = 1.5;\n"
      "  endspecify\n"
      "endmodule\n", 14203);
}

// Test 4: $setuphold timing check
TEST(SpecifyCompleteTest, SetupHoldTimingCheck) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input clk, data);\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 1.5, 2.0);\n"
      "  endspecify\n"
      "endmodule\n", 14204);
}

// Test 5: $recrem timing check
TEST(SpecifyCompleteTest, RecremTimingCheck) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $recrem(posedge rst, posedge clk, 1.0, 1.5);\n"
      "  endspecify\n"
      "endmodule\n", 14205);
}

// Test 6: Conditional path with if
TEST(SpecifyCompleteTest, ConditionalPathWithIf) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input sel, a, output b);\n"
      "  specify\n"
      "    if (sel == 0) (a => b) = 1.2;\n"
      "    if (sel == 1) (a => b) = 2.3;\n"
      "  endspecify\n"
      "endmodule\n", 14206);
}

// Test 7: Edge-sensitive path (posedge/negedge)
TEST(SpecifyCompleteTest, EdgeSensitivePath) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input clk, d, output q);\n"
      "  specify\n"
      "    (posedge clk => (q +: d)) = (1.5, 2.0);\n"
      "    (negedge clk => (q -: d)) = (1.8, 2.2);\n"
      "  endspecify\n"
      "endmodule\n", 14207);
}

// Test 8: Polarity operators (+, - for simple paths; +: -: for edge paths)
TEST(SpecifyCompleteTest, PolarityOperators) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input a, b, output y);\n"
      "  specify\n"
      "    (a +=> y) = 1.0;\n"
      "    (b -=> y) = 1.5;\n"
      "  endspecify\n"
      "endmodule\n", 14208);
}

// Test 9: State-dependent path with ifnone
TEST(SpecifyCompleteTest, StateDependentWithIfnone) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input mode, a, output b);\n"
      "  specify\n"
      "    if (mode) (a *> b) = 1.5;\n"
      "    ifnone (a *> b) = 2.0;\n"
      "  endspecify\n"
      "endmodule\n", 14209);
}

// Test 10: Multiple specify blocks
TEST(SpecifyCompleteTest, MultipleSpecifyBlocks) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input a, b, output y, z);\n"
      "  specify\n"
      "    (a => y) = 1.0;\n"
      "  endspecify\n"
      "  specify\n"
      "    (b => z) = 2.0;\n"
      "  endspecify\n"
      "endmodule\n", 14210);
}

}  // namespace
}  // namespace verilog

