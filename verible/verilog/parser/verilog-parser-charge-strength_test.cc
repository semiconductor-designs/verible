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

// Tests for charge strength (highz0/highz1) and capacitor strength
// (small/medium/large) with trireg nets (M4 Group 2)

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Capacitor strength tests (small/medium/large) - already exist in grammar
TEST(VerilogParserChargeStrengthTest, TriregSmall) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (small) net1; endmodule\n", 0);
}

TEST(VerilogParserChargeStrengthTest, TriregMedium) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (medium) net2; endmodule\n", 1);
}

TEST(VerilogParserChargeStrengthTest, TriregLarge) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (large) net3; endmodule\n", 2);
}

// High-impedance strength tests (highz0/highz1) - need to add to grammar
TEST(VerilogParserChargeStrengthTest, TriregHighz0) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (highz0) net1; endmodule\n", 3);
}

TEST(VerilogParserChargeStrengthTest, TriregHighz1) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (highz1) net2; endmodule\n", 4);
}

// With dimensions
TEST(VerilogParserChargeStrengthTest, TriregSmallWithDimensions) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (small) [7:0] bus; endmodule\n", 5);
}

TEST(VerilogParserChargeStrengthTest, TriregHighz0WithDimensions) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (highz0) [15:0] data; endmodule\n", 6);
}

// With delays
TEST(VerilogParserChargeStrengthTest, TriregSmallWithDelay) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (small) #10 net1; endmodule\n", 7);
}

TEST(VerilogParserChargeStrengthTest, TriregHighz1WithDelay) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (highz1) #5 net2; endmodule\n", 8);
}

// With both dimensions and delays
TEST(VerilogParserChargeStrengthTest, TriregLargeWithBoth) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (large) [3:0] #20 bus; endmodule\n", 9);
}

TEST(VerilogParserChargeStrengthTest, TriregHighz0WithBoth) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (highz0) [31:0] #15 wide_bus; endmodule\n", 10);
}

// Multiple nets in one declaration
TEST(VerilogParserChargeStrengthTest, TriregSmallMultipleNets) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (small) net1, net2, net3; endmodule\n", 11);
}

TEST(VerilogParserChargeStrengthTest, TriregHighz1MultipleNets) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (highz1) net1, net2; endmodule\n", 12);
}

// Without charge strength (should still work)
TEST(VerilogParserChargeStrengthTest, TriregNoStrength) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg [7:0] net1; endmodule\n", 13);
}

// Complex example
TEST(VerilogParserChargeStrengthTest, TriregComplexDeclaration) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trireg (medium) [15:0] #10 data_bus, ctrl_bus; endmodule\n", 14);
}

}  // namespace
}  // namespace verilog

