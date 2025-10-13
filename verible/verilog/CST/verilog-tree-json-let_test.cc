// Copyright 2017-2025 The Verible Authors.
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

#include "verible/verilog/CST/verilog-tree-json.h"

#include <string>

#include "gtest/gtest.h"
#include "verible/common/util/logging.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

#undef ASSERT_OK
#define ASSERT_OK(value) ASSERT_TRUE((value).ok())

namespace verilog {
namespace {

// Helper function to parse and export JSON
std::string GetJSONFromCode(const std::string &code) {
  verilog::VerilogAnalyzer analyzer(code, "<test>");
  auto status = analyzer.Analyze();
  CHECK(status.ok()) << "Parse error: " << status.message();
  
  const auto& text_structure = analyzer.Data();
  const auto* root = text_structure.SyntaxTree().get();
  CHECK(root != nullptr) << "Parse error in test case";
  
  auto json_obj = verilog::ConvertVerilogTreeToJson(*root, text_structure.Contents());
  return json_obj.dump();
}

// Test 1: Basic let declaration
TEST(LetDeclarationTest, BasicLetExpression) {
  const std::string code = R"(
module test;
  let max(a, b) = (a > b) ? a : b;
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("let") != std::string::npos) 
    << "Should contain 'let' keyword in JSON";
}

// Test 2: Let with multiple parameters
TEST(LetDeclarationTest, LetWithMultipleParams) {
  const std::string code = R"(
module test;
  let sum3(x, y, z) = x + y + z;
  
  property p;
    @(posedge clk) sum3(a, b, c) < 100;
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("let") != std::string::npos);
  EXPECT_TRUE(json.find("sum3") != std::string::npos);
}

// Test 3: Multiple let declarations
TEST(LetDeclarationTest, MultipleLets) {
  const std::string code = R"(
module test;
  let valid_range(x) = (x >= 0 && x <= 255);
  let is_power_of_two(x) = (x & (x-1)) == 0;
  let clamp(x, min, max) = (x < min) ? min : (x > max) ? max : x;
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("let") != std::string::npos);
  EXPECT_TRUE(json.find("valid_range") != std::string::npos);
}

// Test 4: Complex let expression
TEST(LetDeclarationTest, ComplexLetExpression) {
  const std::string code = R"(
module test;
  let abs_diff(a, b) = (a > b) ? (a - b) : (b - a);
  let within_threshold(x, y, thresh) = abs_diff(x, y) <= thresh;
  
  property tolerance_check;
    @(posedge clk) within_threshold(signal_a, signal_b, 10);
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("let") != std::string::npos);
  EXPECT_TRUE(json.find("abs_diff") != std::string::npos);
}

// Test 5: Let with bitwise operations
TEST(LetDeclarationTest, LetWithBitwiseOps) {
  const std::string code = R"(
module test;
  let mask_bits(x, mask) = x & mask;
  let set_bit(x, pos) = x | (1 << pos);
  let clear_bit(x, pos) = x & ~(1 << pos);
  
  property check_masked;
    @(posedge clk) mask_bits(data, 8'hFF) == expected;
  endproperty
endmodule
)";

  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("let") != std::string::npos);
  EXPECT_TRUE(json.find("mask_bits") != std::string::npos);
}

}  // namespace
}  // namespace verilog

