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

// Tests for advanced temporal operators in SystemVerilog Assertions
// IEEE 1800-2017 Section 16.10: Cycle delay operators
// M13 Sprint 5: Temporal operators with ranges

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: s_until with range
TEST(TemporalAdvancedTest, SUntilWithRange) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic a, b;\n"
      "  property p;\n"
      "    a s_until[3:5] b;\n"
      "  endproperty\n"
      "endmodule\n", 13501);
}

// Test 2: always with range
TEST(TemporalAdvancedTest, AlwaysWithRange) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic valid, ready;\n"
      "  property p;\n"
      "    always[0:10] (valid |-> ready);\n"
      "  endproperty\n"
      "endmodule\n", 13502);
}

// Test 3: Cycle delay with range
TEST(TemporalAdvancedTest, CycleDelayWithRange) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic req, ack;\n"
      "  property p;\n"
      "    req |-> ##[1:10] ack;\n"
      "  endproperty\n"
      "endmodule\n", 13503);
}

// Test 4: Unbounded range
TEST(TemporalAdvancedTest, UnboundedRange) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic req, done;\n"
      "  property p;\n"
      "    req |-> ##[1:$] eventually done;\n"
      "  endproperty\n"
      "endmodule\n", 13504);
}

// Test 5: Multiple ranges in sequence
TEST(TemporalAdvancedTest, MultipleRangesInSequence) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic a, b, c;\n"
      "  sequence s;\n"
      "    a ##[1:5] b ##[2:8] c;\n"
      "  endsequence\n"
      "endmodule\n", 13505);
}

// Test 6: Complex temporal with ranges
TEST(TemporalAdvancedTest, ComplexTemporalWithRanges) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  property p;\n"
      "    (a s_until[1:3] b) |-> ##[5:10] (c until d);\n"
      "  endproperty\n"
      "endmodule\n", 13506);
}

}  // namespace
}  // namespace verilog

