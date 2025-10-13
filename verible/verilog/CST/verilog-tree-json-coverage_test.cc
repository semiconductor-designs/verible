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

// Phase 3: Functional Coverage Tests for JSON Export
// Tests for covergroup, coverpoint, cross, bins

#include "verible/verilog/CST/verilog-tree-json.h"

#include <string>

#include "gtest/gtest.h"
#include "nlohmann/json.hpp"
#include "verible/common/text/symbol.h"
#include "verible/common/util/logging.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

using nlohmann::json;

namespace verilog {
namespace {

// Helper: Parse code and convert to JSON
json ParseToJson(const std::string& code) {
  VerilogAnalyzer analyzer(code, "<test>");
  auto status = analyzer.Analyze();
  if (!status.ok()) {
    LOG(ERROR) << "Parse error: " << status.message();
    return json::object();
  }
  
  const auto& text_structure = analyzer.Data();
  const auto* root = text_structure.SyntaxTree().get();
  if (!root) return json::object();
  
  return ConvertVerilogTreeToJson(*root, text_structure.Contents());
}

// Helper: Find node by tag recursively
const json* FindNodeByTag(const json& node, const std::string& tag) {
  if (node.contains("tag") && node["tag"] == tag) {
    return &node;
  }
  
  if (node.contains("children")) {
    for (const auto& child : node["children"]) {
      const json* result = FindNodeByTag(child, tag);
      if (result) return result;
    }
  }
  
  return nullptr;
}

// Test 1: Basic covergroup
TEST(CoverageTest, BasicCovergroup) {
  const std::string code = R"(
module test;
  logic [1:0] state;
  
  covergroup cg;
    coverpoint state;
  endgroup
  
  cg cg_inst = new();
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty()) << "Parse should succeed";
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr) << "Should find kCovergroupDeclaration node";
}

// Test 2: Covergroup with trigger event
TEST(CoverageTest, CovergroupWithTriggerEvent) {
  const std::string code = R"(
module test;
  logic clk;
  logic [1:0] state;
  
  covergroup cg @(posedge clk);
    coverpoint state;
  endgroup
  
  cg cg_inst = new();
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 3: Simple coverpoint
TEST(CoverageTest, SimpleCoverpoint) {
  const std::string code = R"(
module test;
  logic [7:0] data;
  
  covergroup cg;
    data_cp: coverpoint data;
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 4: Coverpoint with bins
TEST(CoverageTest, CoverpointWithBins) {
  const std::string code = R"(
module test;
  logic [1:0] state;
  
  covergroup cg;
    coverpoint state {
      bins idle = {0};
      bins busy = {1};
      bins done = {2};
    }
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 5: Coverpoint with bin ranges
TEST(CoverageTest, CoverpointWithBinRanges) {
  const std::string code = R"(
module test;
  logic [7:0] data;
  
  covergroup cg;
    coverpoint data {
      bins low = {[0:63]};
      bins mid = {[64:127]};
      bins high = {[128:255]};
    }
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 6: Coverpoint with illegal_bins
TEST(CoverageTest, CoverpointWithIllegalBins) {
  const std::string code = R"(
module test;
  logic [1:0] state;
  
  covergroup cg;
    coverpoint state {
      bins valid = {0, 1, 2};
      illegal_bins invalid = {3};
    }
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 7: Coverpoint with ignore_bins
TEST(CoverageTest, CoverpointWithIgnoreBins) {
  const std::string code = R"(
module test;
  logic [7:0] data;
  
  covergroup cg;
    coverpoint data {
      bins valid = {[0:254]};
      ignore_bins reserved = {255};
    }
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 8: Coverpoint with wildcard
TEST(CoverageTest, CoverpointWithWildcard) {
  const std::string code = R"(
module test;
  logic [3:0] opcode;
  
  covergroup cg;
    coverpoint opcode {
      wildcard bins load = {4'b00??};
      wildcard bins store = {4'b01??};
    }
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 9: Coverpoint with iff condition
TEST(CoverageTest, CoverpointWithIff) {
  const std::string code = R"(
module test;
  logic valid;
  logic [7:0] data;
  
  covergroup cg;
    coverpoint data iff (valid) {
      bins all = {[0:255]};
    }
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 10: Cross coverage (2 coverpoints)
TEST(CoverageTest, CrossCoverage) {
  const std::string code = R"(
module test;
  logic [1:0] state;
  logic [7:0] data;
  
  covergroup cg;
    state_cp: coverpoint state;
    data_cp: coverpoint data;
    
    cross state_cp, data_cp;
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 11: Cross with ignore_bins
TEST(CoverageTest, CrossWithIgnoreBins) {
  const std::string code = R"(
module test;
  logic [1:0] state;
  logic [7:0] data;
  
  covergroup cg;
    state_cp: coverpoint state {
      bins idle = {0};
      bins busy = {1};
    }
    data_cp: coverpoint data {
      bins low = {[0:127]};
      bins high = {[128:255]};
    }
    
    cross state_cp, data_cp {
      ignore_bins idle_high = binsof(state_cp.idle) && binsof(data_cp.high);
    }
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 12: Cross with binsof
TEST(CoverageTest, CrossWithBinsof) {
  const std::string code = R"(
module test;
  logic [1:0] mode;
  logic [7:0] value;
  
  covergroup cg;
    mode_cp: coverpoint mode;
    value_cp: coverpoint value;
    
    cross mode_cp, value_cp {
      bins valid_combo = binsof(mode_cp) && binsof(value_cp);
    }
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 13: Covergroup with option.per_instance
TEST(CoverageTest, CovergroupWithOptions) {
  const std::string code = R"(
module test;
  logic [1:0] state;
  
  covergroup cg;
    option.per_instance = 1;
    coverpoint state;
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 14: Covergroup with type_option
TEST(CoverageTest, CovergroupWithTypeOption) {
  const std::string code = R"(
module test;
  logic [1:0] state;
  
  covergroup cg;
    type_option.weight = 10;
    coverpoint state;
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 15: Covergroup with multiple coverpoints
TEST(CoverageTest, CovergroupWithMultipleCoverpoints) {
  const std::string code = R"(
module test;
  logic [1:0] state;
  logic [7:0] data;
  logic valid;
  
  covergroup cg;
    state_cp: coverpoint state;
    data_cp: coverpoint data;
    valid_cp: coverpoint valid;
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 16: Covergroup instantiation
TEST(CoverageTest, CovergroupInstantiation) {
  const std::string code = R"(
module test;
  logic clk;
  logic [1:0] state;
  
  covergroup cg @(posedge clk);
    coverpoint state;
  endgroup
  
  cg cg_inst;
  
  initial begin
    cg_inst = new();
  end
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 17: Covergroup with formal arguments
TEST(CoverageTest, CovergroupWithArguments) {
  const std::string code = R"(
module test;
  logic [7:0] data;
  
  covergroup cg(int threshold);
    coverpoint data {
      bins low = {[0:threshold]};
      bins high = {[threshold+1:255]};
    }
  endgroup
  
  cg cg_inst = new(127);
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 18: Nested bins (arrays)
TEST(CoverageTest, NestedBins) {
  const std::string code = R"(
module test;
  logic [7:0] addr;
  
  covergroup cg;
    coverpoint addr {
      bins page0[] = {[0:15]};
      bins page1[] = {[16:31]};
    }
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 19: Transition bins
TEST(CoverageTest, TransitionBins) {
  const std::string code = R"(
module test;
  logic [1:0] state;
  
  covergroup cg;
    coverpoint state {
      bins transitions = (0 => 1 => 2);
    }
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 20: Default bin
TEST(CoverageTest, DefaultBin) {
  const std::string code = R"(
module test;
  logic [1:0] state;
  
  covergroup cg;
    coverpoint state {
      bins known = {0, 1, 2};
      bins default_bin = default;
    }
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 21: Auto bins
TEST(CoverageTest, AutoBins) {
  const std::string code = R"(
module test;
  logic [3:0] nibble;
  
  covergroup cg;
    coverpoint nibble {
      bins auto[] = {[0:15]};
    }
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 22: Empty covergroup
TEST(CoverageTest, EmptyCovergroup) {
  const std::string code = R"(
module test;
  covergroup cg;
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 23: Multiple covergroups
TEST(CoverageTest, MultipleCovergroups) {
  const std::string code = R"(
module test;
  logic [1:0] state;
  logic [7:0] data;
  
  covergroup cg1;
    coverpoint state;
  endgroup
  
  covergroup cg2;
    coverpoint data;
  endgroup
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count covergroups
  int cg_count = 0;
  std::function<void(const json&)> count_covergroups = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kCovergroupDeclaration") {
      cg_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_covergroups(child);
      }
    }
  };
  count_covergroups(tree);
  
  EXPECT_EQ(cg_count, 2) << "Should find 2 covergroups";
}

// Test 24: Covergroup in class
TEST(CoverageTest, CovergroupInClass) {
  const std::string code = R"(
class test_class;
  logic [1:0] state;
  
  covergroup cg;
    coverpoint state;
  endgroup
  
  function new();
    cg = new();
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cg = FindNodeByTag(tree, "kCovergroupDeclaration");
  EXPECT_NE(cg, nullptr);
}

// Test 25: Performance test (50 covergroups)
TEST(CoverageTest, PerformanceTest) {
  std::string code = "module test;\n";
  code += "  logic [7:0] data;\n";
  
  // Generate 50 covergroups
  for (int i = 0; i < 50; i++) {
    code += "  covergroup cg" + std::to_string(i) + ";\n";
    code += "    coverpoint data;\n";
    code += "  endgroup\n";
    code += "  \n";
  }
  
  code += "endmodule\n";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count covergroups
  int cg_count = 0;
  std::function<void(const json&)> count_covergroups = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kCovergroupDeclaration") {
      cg_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_covergroups(child);
      }
    }
  };
  count_covergroups(tree);
  
  EXPECT_EQ(cg_count, 50) << "Should find 50 covergroups";
}

}  // namespace
}  // namespace verilog

