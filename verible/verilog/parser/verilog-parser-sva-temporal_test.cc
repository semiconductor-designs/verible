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

// M7: SVA Temporal Operators - Fix edge cases
// Tests for eventually/s_always without range syntax
// Following TDD: These specific edge case tests should fail initially

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// ============================================================================
// Eventually Operator - Edge Cases (TDD)
// ============================================================================

TEST(VerilogParserSVATemporalTest, EventuallyBasicNoRange) {
  // TDD: This should FAIL initially (grammar exists but unreachable)
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; eventually done; endproperty endmodule\n", 0);
}

TEST(VerilogParserSVATemporalTest, EventuallyWithImplication) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; req |-> eventually ack; endproperty endmodule\n", 1);
}

TEST(VerilogParserSVATemporalTest, EventuallyNested) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; eventually (eventually done); endproperty endmodule\n", 2);
}

TEST(VerilogParserSVATemporalTest, EventuallyInAssertion) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; assert property (@(posedge clk) eventually done); endmodule\n", 3);
}

TEST(VerilogParserSVATemporalTest, EventuallyWithSequence) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; eventually (a ##1 b); endproperty endmodule\n", 4);
}

// Eventually with range (should already work from investigation)
TEST(VerilogParserSVATemporalTest, EventuallyWithRange) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; eventually [3:5] signal; endproperty endmodule\n", 5);
}

// ============================================================================
// S_always Operator - Edge Cases (TDD)
// ============================================================================

TEST(VerilogParserSVATemporalTest, SAlwaysBasicNoRange) {
  // TDD: This should FAIL initially (grammar exists but unreachable)
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; s_always signal; endproperty endmodule\n", 10);
}

TEST(VerilogParserSVATemporalTest, SAlwaysWithImplication) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; req |-> s_always valid; endproperty endmodule\n", 11);
}

TEST(VerilogParserSVATemporalTest, SAlwaysNested) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; s_always (s_always done); endproperty endmodule\n", 12);
}

TEST(VerilogParserSVATemporalTest, SAlwaysInAssertion) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; assert property (@(posedge clk) s_always valid); endmodule\n", 13);
}

// S_always with range (should already work from investigation)
TEST(VerilogParserSVATemporalTest, SAlwaysWithRange) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; s_always [1:5] signal; endproperty endmodule\n", 14);
}

// ============================================================================
// Other Temporal Operators - Verification Tests
// These should already work based on investigation results
// ============================================================================

TEST(VerilogParserSVATemporalTest, NexttimeBasic) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; nexttime signal; endproperty endmodule\n", 20);
}

TEST(VerilogParserSVATemporalTest, NexttimeWithIndex) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; nexttime [2] valid; endproperty endmodule\n", 21);
}

TEST(VerilogParserSVATemporalTest, SNexttimeBasic) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; s_nexttime signal; endproperty endmodule\n", 22);
}

TEST(VerilogParserSVATemporalTest, SNexttimeWithIndex) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; s_nexttime [3] data; endproperty endmodule\n", 23);
}

TEST(VerilogParserSVATemporalTest, SEventuallyBasic) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; s_eventually signal; endproperty endmodule\n", 24);
}

TEST(VerilogParserSVATemporalTest, SEventuallyWithRange) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; s_eventually [2:10] done; endproperty endmodule\n", 25);
}

// ============================================================================
// SVA Synchronization Operators - Verification Tests
// These should already work based on investigation results
// ============================================================================

TEST(VerilogParserSVATemporalTest, AcceptOnBasic) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; accept_on (clk) signal; endproperty endmodule\n", 30);
}

TEST(VerilogParserSVATemporalTest, RejectOnBasic) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; reject_on (reset) signal; endproperty endmodule\n", 31);
}

TEST(VerilogParserSVATemporalTest, SyncAcceptOnBasic) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; sync_accept_on (clk) signal; endproperty endmodule\n", 32);
}

TEST(VerilogParserSVATemporalTest, SyncRejectOnBasic) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; sync_reject_on (reset) signal; endproperty endmodule\n", 33);
}

// ============================================================================
// Combined Tests - Real-world Usage
// ============================================================================

TEST(VerilogParserSVATemporalTest, EventuallyAndNexttime) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; eventually nexttime done; endproperty endmodule\n", 40);
}

TEST(VerilogParserSVATemporalTest, SAlwaysAndImplies) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; req implies s_always valid; endproperty endmodule\n", 41);
}

TEST(VerilogParserSVATemporalTest, ComplexTemporal) {
  // Simplified: eventually with logical expression
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; eventually (ack && done); endproperty endmodule\n", 42);
}

TEST(VerilogParserSVATemporalTest, RealWorldExample) {
  // Simplified: Basic property with eventually and implication
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module sva_check(input clk, req, ack);\n"
      "  property p; @(posedge clk) req |-> eventually ack; endproperty\n"
      "  assert property (p);\n"
      "endmodule\n", 43);
}

}  // namespace
}  // namespace verilog

