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

// Tests for checker instantiation (M11 Feature 2)
// IEEE 1800-2017 Section 17: Checkers

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Basic checker instantiation
TEST(CheckerInstTest, BasicInst) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "checker c;\n"
      "endchecker\n"
      "\n"
      "module m;\n"
      "  c inst();\n"
      "endmodule\n", 4001);
}

// Test 2: Checker instantiation with parameters
TEST(CheckerInstTest, ParameterizedInst) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "checker c #(parameter W=8);\n"
      "endchecker\n"
      "\n"
      "module m;\n"
      "  c #(16) inst();\n"
      "endmodule\n", 4002);
}

// Test 3: Multiple checker instances
TEST(CheckerInstTest, MultipleInst) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "checker c;\n"
      "endchecker\n"
      "\n"
      "module m;\n"
      "  c inst1(), inst2();\n"
      "endmodule\n", 4003);
}

// Test 4: Checker with ports
TEST(CheckerInstTest, CheckerWithPorts) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "checker c(input clk, input logic sig);\n"
      "endchecker\n"
      "\n"
      "module m;\n"
      "  logic clk, sig;\n"
      "  c inst(.clk(clk), .sig(sig));\n"
      "endmodule\n", 4004);
}

// Test 5: Checker in generate block
TEST(CheckerInstTest, CheckerInGenerate) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "checker c;\n"
      "endchecker\n"
      "\n"
      "module m;\n"
      "  generate\n"
      "    genvar i;\n"
      "    for (i = 0; i < 4; i++) begin : gen\n"
      "      c inst();\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n", 4005);
}

}  // namespace
}  // namespace verilog

