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

// Tests for complex sequence expressions in SystemVerilog Assertions
// IEEE 1800-2017 Section 16.9: Sequence operations
// M13 Sprint 3: intersect, first_match, throughout, and/or

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Sequence intersect basic
TEST(ComplexSequencesTest, IntersectBasic) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  sequence s;\n"
      "    (a ##[1:5] b) intersect (c ##[2:4] d);\n"
      "  endsequence\n"
      "endmodule\n", 13301);
}

// Test 2: first_match basic
TEST(ComplexSequencesTest, FirstMatchBasic) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic req, ack;\n"
      "  sequence s;\n"
      "    first_match(req ##[1:$] ack);\n"
      "  endsequence\n"
      "endmodule\n", 13302);
}

// Test 3: first_match with comma (variable capture)
TEST(ComplexSequencesTest, FirstMatchWithCapture) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic req, ack, data;\n"
      "  sequence s;\n"
      "    first_match(req ##[1:$] ack, data);\n"
      "  endsequence\n"
      "endmodule\n", 13303);
}

// Test 4: throughout basic
TEST(ComplexSequencesTest, ThroughoutBasic) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic enable, req, ack;\n"
      "  sequence s;\n"
      "    enable throughout (req ##1 ack);\n"
      "  endsequence\n"
      "endmodule\n", 13304);
}

// Test 5: Complex throughout
TEST(ComplexSequencesTest, ThroughoutComplex) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic valid, req, ack, done;\n"
      "  sequence s;\n"
      "    valid throughout (req ##1 ack ##1 done);\n"
      "  endsequence\n"
      "endmodule\n", 13305);
}

// Test 6: Nested intersect
TEST(ComplexSequencesTest, IntersectNested) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  sequence s;\n"
      "    (a intersect b) ##1 (c intersect d);\n"
      "  endsequence\n"
      "endmodule\n", 13306);
}

// Test 7: Combined operators
TEST(ComplexSequencesTest, CombinedOperators) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic a, b, c;\n"
      "  sequence s;\n"
      "    first_match((a throughout b) intersect c);\n"
      "  endsequence\n"
      "endmodule\n", 13307);
}

// Test 8: Sequence with and/or
TEST(ComplexSequencesTest, SequenceAndOr) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  sequence s;\n"
      "    (a ##1 b) and (c ##1 d);\n"
      "  endsequence\n"
      "endmodule\n", 13308);
}

}  // namespace
}  // namespace verilog

