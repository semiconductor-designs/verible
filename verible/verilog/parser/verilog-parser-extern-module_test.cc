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

// Tests for extern module declarations (M11 Feature 5)
// IEEE 1800-2017 Section 33.4: Elaboration system tasks (separate compilation)

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Basic extern module declaration
TEST(ExternModuleTest, BasicDecl) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "extern module ext_mod (input a, output b);\n", 2001);
}

// Test 2: Extern module with parameters
TEST(ExternModuleTest, WithParams) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "extern module ext_mod #(parameter W=8) (input [W-1:0] a);\n", 2002);
}

// Test 3: Extern module then instantiation
TEST(ExternModuleTest, DeclThenInst) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "extern module ext_mod (input a);\n"
      "\n"
      "module m;\n"
      "  logic a;\n"
      "  ext_mod inst(.a(a));\n"
      "endmodule\n", 2003);
}

// Test 4: Multiple extern module declarations
TEST(ExternModuleTest, MultipleDecls) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "extern module mod1 (input a);\n"
      "extern module mod2 (output b);\n", 2004);
}

// Test 5: Extern module with complex ports
TEST(ExternModuleTest, ComplexPorts) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "extern module ext_mod (\n"
      "  input logic clk,\n"
      "  input logic [7:0] data_in,\n"
      "  output logic [7:0] data_out,\n"
      "  output logic valid\n"
      ");\n", 2005);
}

}  // namespace
}  // namespace verilog

