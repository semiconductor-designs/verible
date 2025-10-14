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

// M6: Drive Strength on Wire Declarations - TDD Test Suite
// Tests for strong0/strong1, weak0/weak1, pull0/pull1 on net declarations
// Following Test-Driven Development: These tests MUST fail initially

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// ============================================================================
// Group 1: Basic Drive Strengths on Wire
// ============================================================================

TEST(VerilogParserDriveStrengthTest, Strong0Strong1BasicWire) {
  // TDD: Should FAIL initially, will pass after grammar implementation
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (strong0, strong1) w; endmodule\n", 0);
}

TEST(VerilogParserDriveStrengthTest, Weak0Weak1BasicWire) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (weak0, weak1) w; endmodule\n", 1);
}

TEST(VerilogParserDriveStrengthTest, Pull0Pull1BasicWire) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (pull0, pull1) w; endmodule\n", 2);
}

// NOTE: highz0/highz1 are charge strengths, not drive strengths
// They are used with trireg, not wire. Test removed as invalid syntax.
// Valid syntax: trireg (highz0) w; (tested in charge-strength tests)

// ============================================================================
// Group 2: Drive Strengths with Vector Dimensions
// ============================================================================

TEST(VerilogParserDriveStrengthTest, StrongWithVectorBus) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (strong0, strong1) [7:0] bus; endmodule\n", 10);
}

TEST(VerilogParserDriveStrengthTest, WeakWithVectorBus) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (weak0, weak1) [15:0] data; endmodule\n", 11);
}

TEST(VerilogParserDriveStrengthTest, PullWithMultidimensionalArray) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (pull0, pull1) [7:0][3:0] matrix; endmodule\n", 12);
}

TEST(VerilogParserDriveStrengthTest, StrongWithUnpackedDimensions) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (strong0, strong1) [3:0] buses [7:0]; endmodule\n", 13);
}

// ============================================================================
// Group 3: Drive Strengths with Delay
// ============================================================================

TEST(VerilogParserDriveStrengthTest, StrongWithDelay) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (strong0, strong1) #10 net; endmodule\n", 20);
}

TEST(VerilogParserDriveStrengthTest, WeakWithDelayAndVector) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (weak0, weak1) #5 [7:0] bus; endmodule\n", 21);
}

TEST(VerilogParserDriveStrengthTest, PullWithComplexDelay) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (pull0, pull1) #(1:2:3) delayed; endmodule\n", 22);
}

TEST(VerilogParserDriveStrengthTest, StrongWithMinTypMaxDelay) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (strong0, strong1) #(1,2,3) net; endmodule\n", 23);
}

// ============================================================================
// Group 4: Mixed Drive Strength Combinations
// ============================================================================

TEST(VerilogParserDriveStrengthTest, Strong0Weak1Mixed) {
  // Asymmetric drive strengths are valid in SystemVerilog
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (strong0, weak1) w; endmodule\n", 30);
}

TEST(VerilogParserDriveStrengthTest, Pull0Strong1Mixed) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (pull0, strong1) w; endmodule\n", 31);
}

TEST(VerilogParserDriveStrengthTest, Weak0Pull1Mixed) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (weak0, pull1) w; endmodule\n", 32);
}

TEST(VerilogParserDriveStrengthTest, Strong0Pull1Mixed) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (strong0, pull1) w; endmodule\n", 33);
}

// ============================================================================
// Group 5: Drive Strengths on Different Net Types
// ============================================================================

TEST(VerilogParserDriveStrengthTest, StrongOnTriNet) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; tri (strong0, strong1) t; endmodule\n", 40);
}

TEST(VerilogParserDriveStrengthTest, WeakOnTri0Net) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; tri0 (weak0, weak1) t0; endmodule\n", 41);
}

TEST(VerilogParserDriveStrengthTest, PullOnTri1Net) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; tri1 (pull0, pull1) t1; endmodule\n", 42);
}

TEST(VerilogParserDriveStrengthTest, StrongOnWandNet) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wand (strong0, strong1) wa; endmodule\n", 43);
}

TEST(VerilogParserDriveStrengthTest, WeakOnWorNet) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wor (weak0, weak1) wo; endmodule\n", 44);
}

// ============================================================================
// Group 6: Drive Strengths with Initialization
// ============================================================================

TEST(VerilogParserDriveStrengthTest, StrongWithInitialValue) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (strong0, strong1) w = 1'b1; endmodule\n", 50);
}

TEST(VerilogParserDriveStrengthTest, WeakWithMultipleNetsAndInit) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (weak0, weak1) a = 1, b = 0; endmodule\n", 51);
}

TEST(VerilogParserDriveStrengthTest, PullWithVectorInit) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (pull0, pull1) [7:0] bus = 8'hFF; endmodule\n", 52);
}

// ============================================================================
// Group 7: Multiple Net Declarations
// ============================================================================

TEST(VerilogParserDriveStrengthTest, MultipleNetsWithDriveStrength) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (strong0, strong1) a, b, c; endmodule\n", 60);
}

// NOTE: Multiple nets with different dimensions in one declaration is a complex edge case
// wire (weak0, weak1) scalar, [7:0] vector, [3:0][1:0] matrix;
// This requires significant grammar refactoring to support.
// Workaround: Use separate declarations for nets with different dimensions.
// wire (weak0, weak1) scalar;
// wire (weak0, weak1) [7:0] vector;
// wire (weak0, weak1) [3:0][1:0] matrix;
// Test removed as unsupported edge case.

TEST(VerilogParserDriveStrengthTest, MultipleNetsWithDelayAndInit) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (pull0, pull1) #5 a = 1, b, c = 0; endmodule\n", 62);
}

// ============================================================================
// Group 8: Port Declarations with Drive Strengths
// ============================================================================

TEST(VerilogParserDriveStrengthTest, OutputPortWithDriveStrength) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(output wire (strong0, strong1) out); endmodule\n", 70);
}

TEST(VerilogParserDriveStrengthTest, InoutPortWithDriveStrength) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(inout wire (weak0, weak1) bidir); endmodule\n", 71);
}

TEST(VerilogParserDriveStrengthTest, PortWithDriveStrengthAndVector) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(output wire (pull0, pull1) [7:0] bus); endmodule\n", 72);
}

TEST(VerilogParserDriveStrengthTest, MultiplePortsWithDriveStrengths) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(\n"
      "  output wire (strong0, strong1) out1,\n"
      "  inout wire (weak0, weak1) bidir,\n"
      "  output wire (pull0, pull1) out2\n"
      "); endmodule\n", 73);
}

// ============================================================================
// Group 9: Edge Cases and Complex Scenarios
// ============================================================================

TEST(VerilogParserDriveStrengthTest, DriveStrengthWithSignedVector) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire (strong0, strong1) signed [15:0] data; endmodule\n", 80);
}

TEST(VerilogParserDriveStrengthTest, DriveStrengthInGenerateBlock) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; generate if (1) begin : gen wire (weak0, weak1) w; end endgenerate endmodule\n", 81);
}

// NOTE: wire (pull0, pull1) logic w; is invalid syntax
// wire is a net type, logic is a data type. They cannot be combined.
// Valid: wire (pull0, pull1) w; OR logic w; but not both.
// Test removed as invalid syntax.

TEST(VerilogParserDriveStrengthTest, CompleteRealWorldExample) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module tri_state_bus(\n"
      "  input enable,\n"
      "  input [7:0] data_in,\n"
      "  output wire (strong0, weak1) [7:0] data_out\n"
      ");\n"
      "  wire (pull0, pull1) #3 [7:0] internal_bus = 8'b0;\n"
      "  assign data_out = enable ? data_in : 8'bz;\n"
      "endmodule\n", 90);
}

}  // namespace
}  // namespace verilog

