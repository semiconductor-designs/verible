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

#include <string>

#include "gtest/gtest.h"
#include "verible/common/util/logging.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/CST/verilog-tree-json.h"

namespace verilog {
namespace {

using verible::TextStructureView;

// Helper function to parse code and export to JSON
std::string GetJSONFromCode(const std::string& code) {
  verilog::VerilogAnalyzer analyzer(code, "<test>");
  auto status = analyzer.Analyze();
  if (!status.ok()) {
    return "";
  }
  const auto& text_structure = analyzer.Data();
  const auto& syntax_tree = text_structure.SyntaxTree();
  if (syntax_tree == nullptr) {
    return "";
  }
  auto json = ConvertVerilogTreeToJson(*syntax_tree, text_structure.Contents());
  return json.dump();
}

// Test 1: Basic specify block
TEST(VerilogTreeJSONSpecifyTest, BasicSpecify) {
  const std::string code = R"(
module test(input a, output b);
  specify
    (a => b) = (1.0, 2.0);
  endspecify
endmodule
)";
  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("specify") != std::string::npos);
  EXPECT_TRUE(json.find("endspecify") != std::string::npos);
}

// Test 2: Specify with pulsestyle_onevent
TEST(VerilogTreeJSONSpecifyTest, PulseStyleOnevent) {
  const std::string code = R"(
module test(input a, output b);
  specify
    pulsestyle_onevent a;
  endspecify
endmodule
)";
  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("specify") != std::string::npos);
  EXPECT_TRUE(json.find("pulsestyle_onevent") != std::string::npos);
}

// Test 3: Specify with pulsestyle_ondetect
TEST(VerilogTreeJSONSpecifyTest, PulseStyleOndetect) {
  const std::string code = R"(
module test(input a, output b);
  specify
    pulsestyle_ondetect b;
  endspecify
endmodule
)";
  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("specify") != std::string::npos);
  EXPECT_TRUE(json.find("pulsestyle_ondetect") != std::string::npos);
}

// Test 4: Specify with showcancelled
TEST(VerilogTreeJSONSpecifyTest, ShowCancelled) {
  const std::string code = R"(
module test(input a, output b);
  specify
    showcancelled a;
  endspecify
endmodule
)";
  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("specify") != std::string::npos);
  EXPECT_TRUE(json.find("showcancelled") != std::string::npos);
}

// Test 5: Specify with noshowcancelled
TEST(VerilogTreeJSONSpecifyTest, NoShowCancelled) {
  const std::string code = R"(
module test(input a, output b);
  specify
    noshowcancelled b;
  endspecify
endmodule
)";
  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("specify") != std::string::npos);
  EXPECT_TRUE(json.find("noshowcancelled") != std::string::npos);
}

// Test 6: Complex specify with multiple statements
TEST(VerilogTreeJSONSpecifyTest, ComplexSpecify) {
  const std::string code = R"(
module test(input clk, input data, output reg q);
  specify
    (clk => q) = (1.0, 2.0);
    pulsestyle_onevent clk;
    showcancelled data;
  endspecify
endmodule
)";
  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("specify") != std::string::npos);
  EXPECT_TRUE(json.find("pulsestyle_onevent") != std::string::npos);
  EXPECT_TRUE(json.find("showcancelled") != std::string::npos);
}

}  // namespace
}  // namespace verilog

