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

// Tests for `matches` with member capture in expression contexts
// IEEE 1800-2017 Section 12.5: Pattern matching with variable binding
// This completes the final 5% of M3 implementation

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Member capture in if statement
TEST(MatchesCaptureTest, IfMatchesWithCapture) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  typedef union tagged { int Valid; } data_t;\n"
      "  data_t value;\n"
      "  int x;\n"
      "  initial if (value matches tagged Valid .v) x = v;\n"
      "endmodule\n", 3101);
}

// Test 2: Member capture in while loop
TEST(MatchesCaptureTest, WhileMatchesWithCapture) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  typedef union tagged { int i; } data_t;\n"
      "  data_t data;\n"
      "  int sum;\n"
      "  initial while (data matches tagged i .val) sum += val;\n"
      "endmodule\n", 3102);
}

// Test 3: Member capture in ternary conditional
TEST(MatchesCaptureTest, TernaryMatchesWithCapture) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  typedef union tagged { bit [7:0] Value; } data_t;\n"
      "  data_t x;\n"
      "  bit [7:0] result;\n"
      "  initial result = (x matches tagged Value .v) ? v : 8'h00;\n"
      "endmodule\n", 3103);
}

// Test 4: Member capture with assertion
TEST(MatchesCaptureTest, AssertMatchesWithCapture) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  typedef union tagged { int i; } data_t;\n"
      "  data_t data;\n"
      "  int captured;\n"
      "  initial if (data matches tagged i .v) assert (v > 0);\n"
      "endmodule\n", 3104);
}

// Test 5: Multiple captures in compound statement
TEST(MatchesCaptureTest, CompoundMatchesWithCapture) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  typedef union tagged { int A; bit [7:0] B; } data_t;\n"
      "  data_t x, y;\n"
      "  int a;\n"
      "  bit [7:0] b;\n"
      "  initial begin\n"
      "    if (x matches tagged A .av) a = av;\n"
      "    if (y matches tagged B .bv) b = bv;\n"
      "  end\n"
      "endmodule\n", 3105);
}

// Test 6: Capture in assignment expression
TEST(MatchesCaptureTest, AssignmentMatchesWithCapture) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  typedef union tagged { int Valid; } opt_t;\n"
      "  opt_t opt;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = (opt matches tagged Valid .v) ? v * 2 : 0;\n"
      "  end\n"
      "endmodule\n", 3106);
}

// Test 7: Nested tagged unions with capture
TEST(MatchesCaptureTest, NestedMatchesWithCapture) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  typedef union tagged { int Inner; } inner_t;\n"
      "  typedef union tagged { inner_t Outer; } outer_t;\n"
      "  outer_t data;\n"
      "  inner_t temp;\n"
      "  initial if (data matches tagged Outer .v) temp = v;\n"
      "endmodule\n", 3107);
}

// Test 8: Capture in do-while loop
TEST(MatchesCaptureTest, DoWhileMatchesWithCapture) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  typedef union tagged { int i; } data_t;\n"
      "  data_t data;\n"
      "  int count;\n"
      "  initial do count++; while (data matches tagged i .v && v > 0);\n"
      "endmodule\n", 3108);
}

// Test 9: Capture with logical AND
TEST(MatchesCaptureTest, LogicalAndWithCapture) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  typedef union tagged { int Value; } data_t;\n"
      "  data_t x;\n"
      "  bit flag;\n"
      "  initial if ((x matches tagged Value .v) && (v > 5)) flag = 1;\n"
      "endmodule\n", 3109);
}

// Test 10: Capture with logical OR
TEST(MatchesCaptureTest, LogicalOrWithCapture) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  typedef union tagged { int A; int B; } data_t;\n"
      "  data_t x;\n"
      "  int result;\n"
      "  initial if ((x matches tagged A .a) || (x matches tagged B .b))\n"
      "    result = 1;\n"
      "endmodule\n", 3110);
}

}  // namespace
}  // namespace verilog

