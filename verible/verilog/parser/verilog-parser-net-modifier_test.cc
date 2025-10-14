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

// Tests for scalared/vectored net array modifiers (M4 Group 1)

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Basic scalared tests
TEST(VerilogParserNetModifierTest, BasicScalaredWire) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire scalared [7:0] bus; endmodule\n", 0);
}

TEST(VerilogParserNetModifierTest, BasicScalaredTri) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; tri scalared [15:0] data; endmodule\n", 1);
}

TEST(VerilogParserNetModifierTest, ScalaredWithWide) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire scalared [31:0] wide_bus; endmodule\n", 2);
}

// Basic vectored tests
TEST(VerilogParserNetModifierTest, BasicVectoredWire) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire vectored [7:0] bus; endmodule\n", 3);
}

TEST(VerilogParserNetModifierTest, BasicVectoredTri) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; tri vectored [15:0] data; endmodule\n", 4);
}

TEST(VerilogParserNetModifierTest, VectoredWithWide) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire vectored [63:0] huge_bus; endmodule\n", 5);
}

// Different net types with scalared
TEST(VerilogParserNetModifierTest, ScalaredTri0) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; tri0 scalared [3:0] low_net; endmodule\n", 6);
}

TEST(VerilogParserNetModifierTest, ScalaredTri1) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; tri1 scalared [3:0] high_net; endmodule\n", 7);
}

TEST(VerilogParserNetModifierTest, ScalaredWand) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wand scalared [7:0] wand_net; endmodule\n", 8);
}

TEST(VerilogParserNetModifierTest, ScalaredWor) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wor scalared [7:0] wor_net; endmodule\n", 9);
}

// Different net types with vectored
TEST(VerilogParserNetModifierTest, VectoredTriand) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; triand vectored [7:0] triand_net; endmodule\n", 10);
}

TEST(VerilogParserNetModifierTest, VectoredTrior) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; trior vectored [7:0] trior_net; endmodule\n", 11);
}

TEST(VerilogParserNetModifierTest, VectoredSupply0) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; supply0 vectored [7:0] ground; endmodule\n", 12);
}

TEST(VerilogParserNetModifierTest, VectoredSupply1) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; supply1 vectored [7:0] power; endmodule\n", 13);
}

// Module ports with modifiers
TEST(VerilogParserNetModifierTest, ScalaredInPort) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(input wire scalared [7:0] data_in); endmodule\n", 14);
}

TEST(VerilogParserNetModifierTest, VectoredOutPort) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(output tri vectored [15:0] data_out); endmodule\n", 15);
}

TEST(VerilogParserNetModifierTest, ScalaredInoutPort) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m(inout wire scalared [31:0] bidir); endmodule\n", 16);
}

// Without packed dimensions (should still parse - modifier is optional)
TEST(VerilogParserNetModifierTest, NoModifierWire) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; wire [7:0] bus; endmodule\n", 17);
}

// Note: The following cases would be semantic errors (detected by semantic checker),
// not syntax errors, so they're not tested here:
// - wire scalared vectored [7:0] bus;  (both modifiers - semantic error)
// - wire scalared bus;                 (modifier without dimensions - semantic error)

}  // namespace
}  // namespace verilog

