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

// M9: Medium Priority Keywords - TDD Test Suite
// Tests for randsequence, untyped, showcancelled, noshowcancelled
// Following TDD: These tests should fail initially

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// ============================================================================
// Randsequence Tests (1 keyword)
// ============================================================================

TEST(VerilogParserM9KeywordsTest, RandsequenceBasic) {
  // TDD: Should FAIL initially
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  initial randsequence(main)\n"
      "    main : first second;\n"
      "    first : { $display(\"first\"); };\n"
      "    second : { $display(\"second\"); };\n"
      "  endsequence\n"
      "endmodule\n", 0);
}

TEST(VerilogParserM9KeywordsTest, RandsequenceWithWeight) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  initial randsequence(main)\n"
      "    main : op1 := 5 | op2 := 3;\n"
      "    op1 : { $display(\"op1\"); };\n"
      "    op2 : { $display(\"op2\"); };\n"
      "  endsequence\n"
      "endmodule\n", 1);
}

TEST(VerilogParserM9KeywordsTest, RandsequenceNested) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  initial randsequence(start)\n"
      "    start : first second done;\n"
      "    first : a | b;\n"
      "    a : { $display(\"a\"); };\n"
      "    b : { $display(\"b\"); };\n"
      "    second : { $display(\"second\"); };\n"
      "    done : { $display(\"done\"); };\n"
      "  endsequence\n"
      "endmodule\n", 2);
}

TEST(VerilogParserM9KeywordsTest, RandsequenceWithIf) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  initial randsequence(main)\n"
      "    main : if (cond) a else b;\n"
      "    a : { $display(\"a\"); };\n"
      "    b : { $display(\"b\"); };\n"
      "  endsequence\n"
      "endmodule\n", 3);
}

TEST(VerilogParserM9KeywordsTest, RandsequenceWithRepeat) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  initial randsequence(main)\n"
      "    main : repeat(5) action;\n"
      "    action : { $display(\"action\"); };\n"
      "  endsequence\n"
      "endmodule\n", 4);
}

// ============================================================================
// Untyped Tests (1 keyword)
// ============================================================================

TEST(VerilogParserM9KeywordsTest, UntypedParameter) {
  // TDD: Should FAIL initially
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m #(parameter untyped p = 5)();\n"
      "endmodule\n", 10);
}

TEST(VerilogParserM9KeywordsTest, UntypedLocalParam) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  localparam untyped lp = 42;\n"
      "endmodule\n", 11);
}

TEST(VerilogParserM9KeywordsTest, UntypedInClass) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "class c;\n"
      "  parameter untyped p = 10;\n"
      "endclass\n", 12);
}

TEST(VerilogParserM9KeywordsTest, UntypedMultipleParams) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m #(\n"
      "  parameter untyped p1 = 1,\n"
      "  parameter untyped p2 = 2\n"
      ")();\n"
      "endmodule\n", 13);
}

// ============================================================================
// Showcancelled / Noshowcancelled Tests (2 keywords)
// ============================================================================

TEST(VerilogParserM9KeywordsTest, ShowcancelledBasic) {
  // TDD: Should FAIL initially
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  specify\n"
      "    showcancelled;\n"
      "  endspecify\n"
      "endmodule\n", 20);
}

TEST(VerilogParserM9KeywordsTest, NoshowcancelledBasic) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  specify\n"
      "    noshowcancelled;\n"
      "  endspecify\n"
      "endmodule\n", 21);
}

TEST(VerilogParserM9KeywordsTest, ShowcancelledWithPath) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input a, output b);\n"
      "  specify\n"
      "    showcancelled;\n"
      "    (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n", 22);
}

TEST(VerilogParserM9KeywordsTest, NoshowcancelledWithPath) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input a, output b);\n"
      "  specify\n"
      "    noshowcancelled;\n"
      "    (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n", 23);
}

TEST(VerilogParserM9KeywordsTest, ShowcancelledMultiple) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input a, b, output c, d);\n"
      "  specify\n"
      "    showcancelled;\n"
      "    (a => c) = 5;\n"
      "    (b => d) = 10;\n"
      "  endspecify\n"
      "endmodule\n", 24);
}

TEST(VerilogParserM9KeywordsTest, ShowcancelledWithPulsestyle) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input a, output b);\n"
      "  specify\n"
      "    pulsestyle_onevent a;\n"
      "    showcancelled;\n"
      "    (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n", 25);
}

// ============================================================================
// Combined Tests - Verify all M9 keywords together
// ============================================================================

TEST(VerilogParserM9KeywordsTest, CombinedRandsequenceAndUntyped) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m #(parameter untyped seed = 42)();\n"
      "  initial randsequence(main)\n"
      "    main : { $display(\"Random test\"); };\n"
      "  endsequence\n"
      "endmodule\n", 30);
}

TEST(VerilogParserM9KeywordsTest, CombinedSpecifyKeywords) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input clk, data, output q);\n"
      "  specify\n"
      "    showcancelled;\n"
      "    pulsestyle_onevent clk;\n"
      "    (clk => q) = (1:2:3, 2:3:4);\n"
      "  endspecify\n"
      "endmodule\n", 31);
}

TEST(VerilogParserM9KeywordsTest, RealWorldRandsequenceTest) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module constraint_randomizer;\n"
      "  bit success;\n"
      "  initial begin\n"
      "    randsequence(test_sequence)\n"
      "      test_sequence : setup test_cases cleanup;\n"
      "      setup : { $display(\"Setup\"); success = 1; };\n"
      "      test_cases : test_a | test_b | test_c;\n"
      "      test_a : { $display(\"Test A\"); };\n"
      "      test_b : { $display(\"Test B\"); };\n"
      "      test_c : { $display(\"Test C\"); };\n"
      "      cleanup : { $display(\"Cleanup\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n", 32);
}

}  // namespace
}  // namespace verilog

