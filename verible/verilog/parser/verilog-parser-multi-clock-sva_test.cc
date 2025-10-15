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

// Tests for multi-clock assertions in SystemVerilog
// IEEE 1800-2017 Section 16.16: Multi-clock support
// M13 Sprint 1: Advanced SVA
// 
// Multi-clock support in SystemVerilog is achieved through:
// 1. Multiple events in event_expression (comma-separated)
// 2. Different clocks on different assertion instances
// 3. Clocking blocks (not tested here)

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Multiple clock events (comma-separated) in single property
TEST(MultiClockSVATest, CommaSeparatedClockEvents) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic clk1, clk2, sig;\n"
      "  property p;\n"
      "    @(posedge clk1, posedge clk2) sig == 1;\n"
      "  endproperty\n"
      "endmodule\n", 13001);
}

// Test 2: Different clocks for different assertions
TEST(MultiClockSVATest, DifferentClocksForDifferentAssertions) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic clk1, clk2, a, b;\n"
      "  sequence s1; a ##1 b; endsequence\n"
      "  assert property (@(posedge clk1) s1);\n"
      "  assert property (@(posedge clk2) s1);\n"
      "endmodule\n", 13002);
}

// Test 3: Multi-clock with negedge
TEST(MultiClockSVATest, MultiClockWithNegedge) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic clk1, clk2, data;\n"
      "  property p;\n"
      "    @(posedge clk1, negedge clk2) data;\n"
      "  endproperty\n"
      "endmodule\n", 13003);
}

// Test 4: Sequence with clock in assertion
TEST(MultiClockSVATest, SequenceWithClockInAssertion) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic clk, req, ack;\n"
      "  sequence s; req ##1 ack; endsequence\n"
      "  assert property (@(posedge clk) s);\n"
      "endmodule\n", 13004);
}

// Test 5: Multiple sequences with different clocks
TEST(MultiClockSVATest, MultipleSequencesWithDifferentClocks) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  logic clk_fast, clk_slow, rst, req, ack;\n"
      "  sequence s_req; req ##1 !req; endsequence\n"
      "  sequence s_ack; ack ##1 !ack; endsequence\n"
      "  assert property (@(posedge clk_fast) disable iff (rst) s_req);\n"
      "  assert property (@(posedge clk_slow) disable iff (rst) s_ack);\n"
      "endmodule\n", 13005);
}

}  // namespace
}  // namespace verilog
