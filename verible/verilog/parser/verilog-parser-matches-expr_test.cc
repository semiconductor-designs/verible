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

// Tests for `matches` keyword in expression contexts (M11 Feature 1)
// IEEE 1800-2017 Section 12.5: Pattern matching conditional expressions

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: matches in if statement (type check without capture)
TEST(MatchesExprTest, IfMatches) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  typedef union tagged { void Invalid; int Valid; } data_t;\n"
      "  data_t value;\n"
      "  initial if (value matches tagged Valid) $display(\"valid\");\n"
      "endmodule\n", 3001);
}

// Test 2: matches in while loop (type check without capture)
TEST(MatchesExprTest, WhileMatches) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  typedef union tagged { int i; } data_t;\n"
      "  data_t data;\n"
      "  int count;\n"
      "  initial while (data matches tagged i) count++;\n"
      "endmodule\n", 3002);
}

// Test 3: matches in ternary conditional
TEST(MatchesExprTest, TernaryMatches) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  int x, y;\n"
      "  initial y = (x matches 5) ? 1 : 0;\n"
      "endmodule\n", 3003);
}

// Test 4: matches with wildcard pattern
TEST(MatchesExprTest, MatchesWithWildcard) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  int x;\n"
      "  bit result;\n"
      "  initial result = (x matches .*) ? 1 : 0;\n"
      "endmodule\n", 3004);
}

// Test 5: matches in assertion (type check without capture)
TEST(MatchesExprTest, MatchesInAssertion) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  typedef union tagged { int i; } data_t;\n"
      "  data_t data;\n"
      "  initial assert (data matches tagged i);\n"
      "endmodule\n", 3005);
}

}  // namespace
}  // namespace verilog

