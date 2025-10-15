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

// Tests for enhanced preprocessor (SV-2023 Feature 3)
// IEEE 1800-2023: Logical operators in ifdef conditionals

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Config with branch filtering enabled (required for expression-based ifdef)
static constexpr VerilogPreprocess::Config kPreprocessConfig{
    .filter_branches = true,
};

// Helper to test code with preprocessor enabled
void TestWithPreprocessor(const char* code) {
  VerilogAnalyzer analyzer(code, "<<inline-test>>", kPreprocessConfig);
  EXPECT_TRUE(analyzer.Analyze().ok()) << "Failed to analyze:\n" << code;
  EXPECT_NE(analyzer.SyntaxTree().get(), nullptr) << "Missing tree for:\n" << code;
}

// Test 1: Logical AND
TEST(EnhancedPreprocessorTest, LogicalAnd) {
  TestWithPreprocessor(
    "`define A\n"
    "`define B\n"
    "`ifdef (A && B)\n"
    "  module m; endmodule\n"
    "`endif\n");
}

// Test 2: Logical OR
TEST(EnhancedPreprocessorTest, LogicalOr) {
  TestWithPreprocessor(
    "`define A\n"
    "`ifdef (A || B)\n"
    "  module m; endmodule\n"
    "`endif\n");
}

// Test 3: Logical NOT
TEST(EnhancedPreprocessorTest, LogicalNot) {
  TestWithPreprocessor(
    "`ifdef (!UNDEFINED)\n"
    "  module m; endmodule\n"
    "`endif\n");
}

// Test 4: Implication
TEST(EnhancedPreprocessorTest, Implication) {
  TestWithPreprocessor(
    "`define MODE\n"
    "`ifdef (MODE -> ADVANCED)\n"
    "  module m; endmodule\n"
    "`endif\n");
}

// Test 5: Equivalence
TEST(EnhancedPreprocessorTest, Equivalence) {
  TestWithPreprocessor(
    "`ifdef (A <-> B)\n"
    "  module m; endmodule\n"
    "`endif\n");
}

// Test 6: Complex expression
TEST(EnhancedPreprocessorTest, ComplexExpression) {
  TestWithPreprocessor(
    "`ifdef ((A && B) || (!C))\n"
    "  module m; endmodule\n"
    "`endif\n");
}

}  // namespace
}  // namespace verilog

