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

// Tests for advanced randsequence features in SystemVerilog
// IEEE 1800-2017 Section 18: Random sequence generation  
// M14 Week 1: Complete randsequence implementation

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Basic randsequence (verify existing)
TEST(RandsequenceAdvancedTest, BasicRandsequence) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : first | second;\n"
      "      first : { $display(\"first\"); };\n"
      "      second : { $display(\"second\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n", 14001);
}

// Test 2: Weighted productions with :=
TEST(RandsequenceAdvancedTest, WeightedProductions) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : first := 5 | second := 3 | third := 2;\n"
      "      first : { $display(\"first\"); };\n"
      "      second : { $display(\"second\"); };\n"
      "      third : { $display(\"third\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n", 14002);
}

// Test 3: Multiple weights in one production
TEST(RandsequenceAdvancedTest, MultipleWeights) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : mode0 := 10 | mode1 := 20 | mode2 := 30 | mode3 := 40;\n"
      "      mode0 : { $display(\"mode0\"); };\n"
      "      mode1 : { $display(\"mode1\"); };\n"
      "      mode2 : { $display(\"mode2\"); };\n"
      "      mode3 : { $display(\"mode3\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n", 14003);
}

// Test 4: Production with arguments
TEST(RandsequenceAdvancedTest, ProductionWithArguments) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : add(1, 2) | subtract(5, 3);\n"
      "      void add(int x, int y) : { $display(\"sum=%0d\", x+y); };\n"
      "      void subtract(int a, int b) : { $display(\"diff=%0d\", a-b); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n", 14004);
}

// Test 5: Case statement in production
TEST(RandsequenceAdvancedTest, CaseInProduction) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  int mode;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (mode)\n"
      "               0: mode0;\n"
      "               1: mode1;\n"
      "               default: mode_default;\n"
      "             endcase;\n"
      "      mode0 : { $display(\"mode 0\"); };\n"
      "      mode1 : { $display(\"mode 1\"); };\n"
      "      mode_default : { $display(\"default\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n", 14005);
}

// Test 6: if-else in production
TEST(RandsequenceAdvancedTest, IfElseInProduction) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  bit done;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (done) finish else action;\n"
      "      action : { $display(\"action\"); };\n"
      "      finish : { $display(\"done\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n", 14006);
}

// Test 7: repeat in production
TEST(RandsequenceAdvancedTest, RepeatInProduction) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat(5) action;\n"
      "      action : { $display(\"repeat action\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n", 14007);
}

// Test 8: rand join (parallel productions)
TEST(RandsequenceAdvancedTest, RandJoin) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join seq1 seq2 seq3;\n"
      "      seq1 : { $display(\"seq1\"); };\n"
      "      seq2 : { $display(\"seq2\"); };\n"
      "      seq3 : { $display(\"seq3\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n", 14008);
}

// Test 9: break statement in production
TEST(RandsequenceAdvancedTest, BreakInProduction) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  int count = 0;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat(10) action;\n"
      "      action : { count++; if (count > 5) break; $display(\"count=%0d\", count); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n", 14009);
}

// Test 10: return statement in production
TEST(RandsequenceAdvancedTest, ReturnInProduction) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  bit early_exit;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : first second;\n"
      "      first : { if (early_exit) return; $display(\"first\"); };\n"
      "      second : { $display(\"second\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n", 14010);
}

}  // namespace
}  // namespace verilog

