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

// Tests for `soft` packed unions (SV-2023 Feature 4)
// IEEE 1800-2023: Allow packed unions with different-sized members

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Basic soft union
TEST(SoftUnionTest, BasicDecl) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m;\n"
    "  typedef union packed soft {\n"
    "    logic [7:0] byte_val;\n"
    "    logic [31:0] word_val;\n"
    "  } data_t;\n"
    "endmodule\n", 5031);
}

// Test 2: Multiple different sizes
TEST(SoftUnionTest, MultipleSizes) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "union packed soft {\n"
    "  bit [3:0] nibble;\n"
    "  bit [15:0] word;\n"
    "  bit [63:0] dword;\n"
    "} flexible;\n", 5032);
}

// Test 3: In typedef
TEST(SoftUnionTest, InTypedef) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "typedef union packed soft {\n"
    "  int i;\n"
    "  longint l;\n"
    "} variant_t;\n", 5033);
}

// Test 4: Anonymous soft union
TEST(SoftUnionTest, Anonymous) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m;\n"
    "  union packed soft {\n"
    "    logic [7:0] a;\n"
    "    logic [15:0] b;\n"
    "  } data;\n"
    "endmodule\n", 5034);
}

}  // namespace
}  // namespace verilog

