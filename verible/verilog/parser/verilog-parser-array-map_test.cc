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

// Tests for array map method (SV-2023 Feature 7)
// IEEE 1800-2023: Array.map() for element-wise operations

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Basic map with lambda
TEST(ArrayMapTest, BasicLambda) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m;\n"
    "  int a[] = {1, 2, 3};\n"
    "  int b[] = a.map(x => x * 2);\n"
    "endmodule\n", 5061);
}

// Test 2: Map with function reference
TEST(ArrayMapTest, FunctionReference) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m;\n"
    "  function int square(int x); return x*x; endfunction\n"
    "  int a[] = {1, 2, 3};\n"
    "  int b[] = a.map(square);\n"
    "endmodule\n", 5062);
}

// Test 3: Complex lambda expression
TEST(ArrayMapTest, ComplexLambda) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m;\n"
    "  int a[], c[];\n"
    "  initial c = a.map(x => (x > 5) ? x : 0);\n"
    "endmodule\n", 5063);
}

// Test 4: Chained map operations
TEST(ArrayMapTest, ChainedMap) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m;\n"
    "  int a[], result[];\n"
    "  initial result = a.map(x => x * 2).map(x => x + 1);\n"
    "endmodule\n", 5064);
}

}  // namespace
}  // namespace verilog

