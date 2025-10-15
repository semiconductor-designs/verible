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

// Tests for recursive properties and sequences in SystemVerilog Assertions
// IEEE 1800-2017 Section 16.5: Recursive properties
// M13 Sprint 4: Recursion and parameters

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Simple recursive sequence with parameter
TEST(RecursivePropertiesTest, SimpleRecursiveSequence) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic req;\n"
      "  sequence s(int n);\n"
      "    (n > 0) ##1 req ##1 s(n-1);\n"
      "  endsequence\n"
      "endmodule\n", 13401);
}

// Test 2: Recursive property with if/else
TEST(RecursivePropertiesTest, RecursivePropertyIfElse) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic req, ack;\n"
      "  property p(int n);\n"
      "    if (n == 0) ack;\n"
      "    else req |-> ##1 p(n-1);\n"
      "  endproperty\n"
      "endmodule\n", 13402);
}

// Test 3: Mutual recursion (forward usage)
TEST(RecursivePropertiesTest, MutualRecursion) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic a, b;\n"
      "  sequence s_a;\n"
      "    a ##1 s_b;\n"
      "  endsequence\n"
      "  sequence s_b;\n"
      "    b ##1 s_a;\n"
      "  endsequence\n"
      "endmodule\n", 13403);
}

// Test 4: Recursive with local variable
TEST(RecursivePropertiesTest, RecursiveWithLocalVar) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic req;\n"
      "  property p(int depth);\n"
      "    int local_d;\n"
      "    (req, local_d = depth) |-> ##1 (local_d > 0) and p(local_d - 1);\n"
      "  endproperty\n"
      "endmodule\n", 13404);
}

// Test 5: Recursive sequence in property
TEST(RecursivePropertiesTest, RecursiveSequenceInProperty) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic req, tick;\n"
      "  sequence countdown(int n);\n"
      "    (n == 0) or (tick ##1 countdown(n-1));\n"
      "  endsequence\n"
      "  property p;\n"
      "    req |-> countdown(5);\n"
      "  endproperty\n"
      "endmodule\n", 13405);
}

// Test 6: Complex recursion with parameters
TEST(RecursivePropertiesTest, ComplexRecursionMultiParam) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic a, b, done;\n"
      "  property nested(int m, int n);\n"
      "    if (m == 0 && n == 0) done;\n"
      "    else if (m > 0) a |-> ##1 nested(m-1, n);\n"
      "    else b |-> ##1 nested(m, n-1);\n"
      "  endproperty\n"
      "endmodule\n", 13406);
}

}  // namespace
}  // namespace verilog

