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

// Test 1: Basic config declaration
TEST(VerilogTreeJSONConfigTest, BasicConfig) {
  const std::string code = R"(
config cfg;
  design work.top;
endconfig
)";
  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("config") != std::string::npos);
  EXPECT_TRUE(json.find("design") != std::string::npos);
}

// Test 2: Config with instance rule
TEST(VerilogTreeJSONConfigTest, ConfigWithInstance) {
  const std::string code = R"(
config cfg;
  design work.top;
  instance top.u1 use work.mod_a;
endconfig
)";
  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("config") != std::string::npos);
  EXPECT_TRUE(json.find("instance") != std::string::npos);
  EXPECT_TRUE(json.find("use") != std::string::npos);
}

// Test 3: Config with cell rule
TEST(VerilogTreeJSONConfigTest, ConfigWithCell) {
  const std::string code = R"(
config cfg;
  design work.top;
  cell work.cell1 liblist lib1;
endconfig
)";
  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("config") != std::string::npos);
  EXPECT_TRUE(json.find("cell") != std::string::npos);
  EXPECT_TRUE(json.find("liblist") != std::string::npos);
}

// Test 4: Complex config with multiple rules
TEST(VerilogTreeJSONConfigTest, ComplexConfig) {
  const std::string code = R"(
config my_cfg;
  design lib1.top_module;
  instance top_module.u1 use lib2.module_a;
  instance top_module.u2 use lib2.module_b;
  cell lib1.cell1 liblist lib3 lib4;
endconfig
)";
  const std::string json = GetJSONFromCode(code);
  EXPECT_TRUE(json.find("config") != std::string::npos);
  EXPECT_TRUE(json.find("my_cfg") != std::string::npos);
  EXPECT_TRUE(json.find("design") != std::string::npos);
  EXPECT_TRUE(json.find("instance") != std::string::npos);
  EXPECT_TRUE(json.find("cell") != std::string::npos);
}

// Test 5: Config declaration is searchable in JSON
TEST(VerilogTreeJSONConfigTest, ConfigMetadataPresent) {
  const std::string code = R"(
config test_config;
  design work.dut;
endconfig
)";
  const std::string json = GetJSONFromCode(code);
  // Verify the config keyword and name are both present
  EXPECT_TRUE(json.find("config") != std::string::npos);
  EXPECT_TRUE(json.find("test_config") != std::string::npos);
  EXPECT_TRUE(json.find("work") != std::string::npos);
}

}  // namespace
}  // namespace verilog

