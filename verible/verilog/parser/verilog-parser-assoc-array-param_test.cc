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

// Tests for associative array parameters (SV-2023 Feature 6)
// IEEE 1800-2023: Support constant associative arrays as module/class parameters

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: String-indexed config (declaration only)
TEST(AssocArrayParamTest, StringIndexedConfig) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m #(parameter int cfg_map[string]);\n"
    "endmodule\n", 5051);
}

// Test 2: Integer-indexed (declaration only)
TEST(AssocArrayParamTest, IntIndexed) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "class C #(parameter string names[int]);\n"
    "endclass\n", 5052);
}

// Test 3: In module instantiation
TEST(AssocArrayParamTest, InInstantiation) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m #(parameter int cfg[string]);\n"
    "endmodule\n"
    "module top;\n"
    "  m #(.cfg('{\"size\": 8})) inst();\n"
    "endmodule\n", 5053);
}

}  // namespace
}  // namespace verilog

