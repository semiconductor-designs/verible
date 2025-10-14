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

// Phase 1: Investigation of 40 blocked keywords
// Tests to verify actual grammar status vs. documentation claims
// Each test is EXPECTED to fail initially to confirm the gap

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// ============================================================================
// HIGH PRIORITY: Drive Strengths (6 keywords)
// ============================================================================

TEST(KeywordInvestigationTest, Strong0OnWireDeclaration) {
  // Expected: FAIL - drive strength on wire not supported
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (strong0, strong1) w; endmodule\n", 0);
}

TEST(KeywordInvestigationTest, Weak0OnWireDeclaration) {
  // Expected: FAIL - drive strength on wire not supported
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (weak0, weak1) w; endmodule\n", 1);
}

TEST(KeywordInvestigationTest, Pull0OnWireDeclaration) {
  // Expected: FAIL - drive strength on wire not supported
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (pull0, pull1) w; endmodule\n", 2);
}

TEST(KeywordInvestigationTest, DriveStrengthWithVector) {
  // Expected: FAIL - drive strength on wire with dimensions
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (strong0, strong1) [7:0] bus; endmodule\n", 3);
}

TEST(KeywordInvestigationTest, DriveStrengthWithDelay) {
  // Expected: FAIL - drive strength on wire with delay
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (weak0, weak1) #10 net; endmodule\n", 4);
}

TEST(KeywordInvestigationTest, MixedDriveStrengths) {
  // Expected: FAIL - mixed drive strengths
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (strong0, pull1) w; endmodule\n", 5);
}

// ============================================================================
// HIGH PRIORITY: SVA Temporal Operators (6 keywords)
// ============================================================================

TEST(KeywordInvestigationTest, EventuallyBasic) {
  // Expected: May work or fail - grammar exists but may be unreachable
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; eventually done; endproperty endmodule\n", 10);
}

TEST(KeywordInvestigationTest, EventuallyWithRange) {
  // Expected: May work or fail
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; eventually [3:5] signal; endproperty endmodule\n", 11);
}

TEST(KeywordInvestigationTest, NexttimeBasic) {
  // Expected: May work or fail
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; nexttime signal; endproperty endmodule\n", 12);
}

TEST(KeywordInvestigationTest, NexttimeWithIndex) {
  // Expected: May work or fail
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; nexttime [2] valid; endproperty endmodule\n", 13);
}

TEST(KeywordInvestigationTest, SAlwaysBasic) {
  // Expected: May work or fail
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; s_always signal; endproperty endmodule\n", 14);
}

TEST(KeywordInvestigationTest, SAlwaysWithRange) {
  // Expected: May work or fail
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; s_always [1:5] signal; endproperty endmodule\n", 15);
}

TEST(KeywordInvestigationTest, SEventuallyBasic) {
  // Expected: May work or fail
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; s_eventually signal; endproperty endmodule\n", 16);
}

TEST(KeywordInvestigationTest, SNexttimeBasic) {
  // Expected: May work or fail
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; s_nexttime signal; endproperty endmodule\n", 17);
}

// ============================================================================
// HIGH PRIORITY: SVA Synchronization (4 keywords)
// ============================================================================

TEST(KeywordInvestigationTest, AcceptOnBasic) {
  // Expected: May work - grammar exists at line 7785
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; accept_on (clk) signal; endproperty endmodule\n", 20);
}

TEST(KeywordInvestigationTest, RejectOnBasic) {
  // Expected: May work - grammar exists at line 7787
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; reject_on (reset) signal; endproperty endmodule\n", 21);
}

TEST(KeywordInvestigationTest, SyncAcceptOnBasic) {
  // Expected: May work - grammar exists at line 7789
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; sync_accept_on (clk) signal; endproperty endmodule\n", 22);
}

TEST(KeywordInvestigationTest, SyncRejectOnBasic) {
  // Expected: May work - grammar exists at line 7791
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; sync_reject_on (reset) signal; endproperty endmodule\n", 23);
}

// ============================================================================
// HIGH PRIORITY: Configuration Blocks (8 keywords)
// ============================================================================

TEST(KeywordInvestigationTest, ConfigBasic) {
  // Expected: FAIL - grammar exists but fails to parse
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "config cfg; design top; endconfig\n", 30);
}

TEST(KeywordInvestigationTest, DesignStatement) {
  // Expected: FAIL - "syntax error at token 'design'"
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "config cfg; design lib.cell; endconfig\n", 31);
}

TEST(KeywordInvestigationTest, InstanceClause) {
  // Expected: FAIL
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "config cfg; design top; instance x use y; endconfig\n", 32);
}

TEST(KeywordInvestigationTest, CellClause) {
  // Expected: FAIL
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "config cfg; design top; cell x use y; endconfig\n", 33);
}

TEST(KeywordInvestigationTest, LiblistClause) {
  // Expected: FAIL
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "config cfg; design top; default liblist lib1; endconfig\n", 34);
}

TEST(KeywordInvestigationTest, LibraryClause) {
  // Expected: FAIL
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "config cfg; design top; instance x liblist lib1; endconfig\n", 35);
}

TEST(KeywordInvestigationTest, UseClause) {
  // Expected: FAIL
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "config cfg; design top; instance x use lib.cell; endconfig\n", 36);
}

TEST(KeywordInvestigationTest, ConfigComplete) {
  // Expected: FAIL - comprehensive config block
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "config cfg;\n"
      "  design work.top;\n"
      "  default liblist lib1 lib2;\n"
      "  instance top.u1 use lib.cell1;\n"
      "endconfig\n", 37);
}

// ============================================================================
// MEDIUM PRIORITY: Randomization (1 keyword)
// ============================================================================

TEST(KeywordInvestigationTest, RandsequenceBasic) {
  // Expected: FAIL or unclear - need to verify
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; initial randsequence() main; endsequence endmodule\n", 40);
}

// ============================================================================
// MEDIUM PRIORITY: Type Keywords (3 keywords)
// ============================================================================

TEST(KeywordInvestigationTest, UntypedBasic) {
  // Expected: May work - need to verify context
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; untyped data; endmodule\n", 41);
}

TEST(KeywordInvestigationTest, Unique0Basic) {
  // Expected: May work - similar to unique
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; initial unique0 case (x) 0: y = 1; endcase endmodule\n", 42);
}

TEST(KeywordInvestigationTest, TypeOperator) {
  // Expected: FAIL - typeof() operator
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; typedef type(x) t; endmodule\n", 43);
}

// ============================================================================
// LOW PRIORITY: Specify Advanced (4 keywords)
// ============================================================================

TEST(KeywordInvestigationTest, PulsestyleOnevent) {
  // Expected: FAIL or unclear
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; specify pulsestyle_onevent a; endspecify endmodule\n", 50);
}

TEST(KeywordInvestigationTest, PulsestyleOndetect) {
  // Expected: FAIL or unclear
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; specify pulsestyle_ondetect b; endspecify endmodule\n", 51);
}

TEST(KeywordInvestigationTest, Showcancelled) {
  // Expected: FAIL or unclear
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; specify showcancelled; endspecify endmodule\n", 52);
}

TEST(KeywordInvestigationTest, Noshowcancelled) {
  // Expected: FAIL or unclear
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; specify noshowcancelled; endspecify endmodule\n", 53);
}

}  // namespace
}  // namespace verilog

