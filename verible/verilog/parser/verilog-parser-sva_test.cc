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

// Tests for SVA operators: until, implies, within (M5 Group 4)
// Verifies existing grammar implementation

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// implies operator tests
TEST(VerilogParserSVATest, ImpliesInProperty) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; a implies b; endproperty endmodule\n", 0);
}

TEST(VerilogParserSVATest, ImpliesWithSequence) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; (req) implies (ack); endproperty endmodule\n", 1);
}

TEST(VerilogParserSVATest, ImpliesInAssertion) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; assert property (@(posedge clk) a implies b); endmodule\n", 2);
}

TEST(VerilogParserSVATest, ImpliesWithDelay) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; a implies ##1 b; endproperty endmodule\n", 3);
}

TEST(VerilogParserSVATest, ImpliesNested) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; a implies (b implies c); endproperty endmodule\n", 4);
}

// until operator tests
TEST(VerilogParserSVATest, UntilInSequence) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; sequence s; a until b; endsequence endmodule\n", 5);
}

TEST(VerilogParserSVATest, UntilInProperty) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; a until b; endproperty endmodule\n", 6);
}

TEST(VerilogParserSVATest, UntilWithExpression) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; req until ack; endproperty endmodule\n", 7);
}

TEST(VerilogParserSVATest, SUntilInSequence) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; sequence s; a s_until b; endsequence endmodule\n", 8);
}

TEST(VerilogParserSVATest, UntilWithInSequence) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; sequence s; a until_with b; endsequence endmodule\n", 9);
}

TEST(VerilogParserSVATest, SUntilWithInSequence) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; sequence s; a s_until_with b; endsequence endmodule\n", 10);
}

// within operator tests
TEST(VerilogParserSVATest, WithinInSequence) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; sequence s; a within b; endsequence endmodule\n", 11);
}

TEST(VerilogParserSVATest, WithinWithSequenceExpr) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; sequence s; (req ##1 ack) within parent_seq; endsequence endmodule\n", 12);
}

TEST(VerilogParserSVATest, WithinInProperty) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; seq1 within seq2; endproperty endmodule\n", 13);
}

// Combined operators
TEST(VerilogParserSVATest, UntilAndImplies) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; (a until b) implies c; endproperty endmodule\n", 14);
}

TEST(VerilogParserSVATest, ImpliesAndWithin) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; a implies (b within c); endproperty endmodule\n", 15);
}

TEST(VerilogParserSVATest, AllThreeOperators) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; (a until b) implies (c within d); endproperty endmodule\n", 16);
}

// In assertions
TEST(VerilogParserSVATest, AssertImplies) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; assert property (@(posedge clk) req implies ack); endmodule\n", 17);
}

TEST(VerilogParserSVATest, AssertUntil) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; assert property (@(posedge clk) req until grant); endmodule\n", 18);
}

TEST(VerilogParserSVATest, AssertWithin) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; assert property (@(posedge clk) trans within cycle); endmodule\n", 19);
}

// Complex patterns
TEST(VerilogParserSVATest, ComplexImpliesChain) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; property p; a implies b implies c implies d; endproperty endmodule\n", 20);
}

TEST(VerilogParserSVATest, ComplexUntilNested) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; sequence s; (a until b) until c; endsequence endmodule\n", 21);
}

TEST(VerilogParserSVATest, ComplexWithinNested) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; sequence s; (a within b) within c; endsequence endmodule\n", 22);
}

TEST(VerilogParserSVATest, RealWorldAssertion1) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; assert property (@(posedge clk) valid implies ##1 ready); endmodule\n", 23);
}

TEST(VerilogParserSVATest, RealWorldAssertion2) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m; assert property (@(posedge clk) (req until ack) implies done); endmodule\n", 24);
}

}  // namespace
}  // namespace verilog

