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

// Test 1: Basic combinational UDP
TEST(VerilogTreeJSONUDPTest, BasicCombinationalUDP) {
  const std::string code = R"(
primitive mux (out, a, b, sel);
  output out;
  input a, b, sel;
  table
    0 ? 0 : 0;
    1 ? 0 : 1;
    ? 0 1 : 0;
    ? 1 1 : 1;
  endtable
endprimitive
)";
  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("primitive") != std::string::npos);
  EXPECT_TRUE(json.find("mux") != std::string::npos);
  EXPECT_TRUE(json.find("table") != std::string::npos);
  EXPECT_TRUE(json.find("endtable") != std::string::npos);
  EXPECT_TRUE(json.find("endprimitive") != std::string::npos);
}

// Test 2: Sequential UDP with initial state
TEST(VerilogTreeJSONUDPTest, SequentialUDP) {
  const std::string code = R"(
primitive dff (q, clk, data);
  output q;
  reg q;
  input clk, data;
  table
    r 0 : ? : 0;
    r 1 : ? : 1;
    f ? : ? : -;
  endtable
endprimitive
)";
  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("primitive") != std::string::npos);
  EXPECT_TRUE(json.find("dff") != std::string::npos);
  EXPECT_TRUE(json.find("table") != std::string::npos);
}

// Test 3: UDP with initial statement
TEST(VerilogTreeJSONUDPTest, UDPWithInitial) {
  const std::string code = R"(
primitive latch (q, enable, data);
  output q;
  reg q;
  input enable, data;
  initial q = 0;
  table
    1 0 : ? : 0;
    1 1 : ? : 1;
    0 ? : ? : -;
  endtable
endprimitive
)";
  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("primitive") != std::string::npos);
  EXPECT_TRUE(json.find("latch") != std::string::npos);
  EXPECT_TRUE(json.find("initial") != std::string::npos);
  EXPECT_TRUE(json.find("table") != std::string::npos);
}

}  // namespace
}  // namespace verilog

