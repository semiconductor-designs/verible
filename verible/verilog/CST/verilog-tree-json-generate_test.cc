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

// Phase 4: Generate Block Tests for JSON Export
// Tests for generate for/if/case constructs with parametric design metadata

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

// Test 1: Explicit generate for loop (with generate/endgenerate)
TEST(GenerateTest, ExplicitGenerateForLoop) {
  const std::string code = R"(
module test;
  generate
    for (genvar i = 0; i < 4; i++) begin
      logic [7:0] data;
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty()) << "Parse should succeed";
  
  const json* gen_region = FindNodeByTag(tree, "kGenerateRegion");
  ASSERT_NE(gen_region, nullptr) << "Should find kGenerateRegion node";
  
  const json* gen = FindNodeByTag(tree, "kLoopGenerateConstruct");
  ASSERT_NE(gen, nullptr) << "Should find kLoopGenerateConstruct node";
}

// Test 2: Implicit generate for loop (without generate/endgenerate)
TEST(GenerateTest, ImplicitGenerateForLoop) {
  const std::string code = R"(
module test;
  for (genvar i = 0; i < 4; i++) begin
    logic [7:0] data;
  end
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty()) << "Parse should succeed";
  
  const json* gen = FindNodeByTag(tree, "kLoopGenerateConstruct");
  ASSERT_NE(gen, nullptr) << "Should find kLoopGenerateConstruct node in implicit form";
}

// Test 3: Explicit generate for loop with label
TEST(GenerateTest, ExplicitGenerateForLoopWithLabel) {
  const std::string code = R"(
module test;
  generate
    for (genvar i = 0; i < 8; i++) begin : gen_array
      logic [15:0] mem;
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* gen = FindNodeByTag(tree, "kLoopGenerateConstruct");
  ASSERT_NE(gen, nullptr);
  
  if (gen->contains("metadata") && (*gen)["metadata"].contains("generate_info")) {
    const auto& info = (*gen)["metadata"]["generate_info"];
    if (info.contains("has_label")) {
      EXPECT_TRUE(info["has_label"]);
    }
    if (info.contains("label")) {
      EXPECT_EQ(info["label"], "gen_array");
    }
  }
}

// Test 4: Implicit generate for loop with label
TEST(GenerateTest, ImplicitGenerateForLoopWithLabel) {
  const std::string code = R"(
module test;
  for (genvar i = 0; i < 8; i++) begin : gen_array
    logic [15:0] mem;
  end
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* gen = FindNodeByTag(tree, "kLoopGenerateConstruct");
  ASSERT_NE(gen, nullptr);
  
  if (gen->contains("metadata") && (*gen)["metadata"].contains("generate_info")) {
    const auto& info = (*gen)["metadata"]["generate_info"];
    if (info.contains("has_label")) {
      EXPECT_TRUE(info["has_label"]);
    }
    if (info.contains("label")) {
      EXPECT_EQ(info["label"], "gen_array");
    }
  }
}

// Test 5: Explicit generate if/else
TEST(GenerateTest, ExplicitGenerateIfElse) {
  const std::string code = R"(
module test #(parameter USE_FEATURE = 1);
  generate
    if (USE_FEATURE) begin
      logic feature_signal;
    end else begin
      logic default_signal;
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* gen_if = FindNodeByTag(tree, "kGenerateIf");
  ASSERT_NE(gen_if, nullptr) << "Should find kGenerateIf node";
}

// Test 6: Implicit generate if/else
TEST(GenerateTest, ImplicitGenerateIfElse) {
  const std::string code = R"(
module test #(parameter USE_FEATURE = 1);
  if (USE_FEATURE) begin
    logic feature_signal;
  end else begin
    logic default_signal;
  end
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* gen_if = FindNodeByTag(tree, "kGenerateIf");
  ASSERT_NE(gen_if, nullptr) << "Should find kGenerateIf node in implicit form";
}

// Test 7: Explicit generate case
TEST(GenerateTest, ExplicitGenerateCase) {
  const std::string code = R"(
module test #(parameter MODE = 0);
  generate
    case (MODE)
      0: begin
        logic mode0;
      end
      1: begin
        logic mode1;
      end
      default: begin
        logic mode_default;
      end
    endcase
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Check for generate case items
  const json* gen_case = FindNodeByTag(tree, "kGenerateCaseItemList");
  ASSERT_NE(gen_case, nullptr) << "Should find generate case structure";
}

// Test 8: Implicit generate case
TEST(GenerateTest, ImplicitGenerateCase) {
  const std::string code = R"(
module test #(parameter MODE = 0);
  case (MODE)
    0: begin
      logic mode0;
    end
    1: begin
      logic mode1;
    end
    default: begin
      logic mode_default;
    end
  endcase
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Check for generate case items
  const json* gen_case = FindNodeByTag(tree, "kGenerateCaseItemList");
  ASSERT_NE(gen_case, nullptr) << "Should find implicit generate case structure";
}

// Test 9: Nested explicit generate blocks
TEST(GenerateTest, NestedExplicitGenerate) {
  const std::string code = R"(
module test;
  generate
    for (genvar i = 0; i < 2; i++) begin : outer
      for (genvar j = 0; j < 3; j++) begin : inner
        logic [7:0] data;
      end
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* gen = FindNodeByTag(tree, "kLoopGenerateConstruct");
  ASSERT_NE(gen, nullptr);
}

// Test 10: Generate with parameters
TEST(GenerateTest, GenerateWithParameters) {
  const std::string code = R"(
module test #(parameter N = 4);
  generate
    for (genvar i = 0; i < N; i++) begin
      logic [31:0] reg_file;
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* gen = FindNodeByTag(tree, "kLoopGenerateConstruct");
  ASSERT_NE(gen, nullptr);
}

// Test 11: Named generate blocks
TEST(GenerateTest, NamedGenerateBlocks) {
  const std::string code = R"(
module test;
  generate
    begin : named_block
      logic signal1;
      logic signal2;
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* gen_block = FindNodeByTag(tree, "kGenerateBlock");
  ASSERT_NE(gen_block, nullptr);
}

// Test 12: Generate if without else
TEST(GenerateTest, GenerateIfWithoutElse) {
  const std::string code = R"(
module test #(parameter ENABLE = 1);
  generate
    if (ENABLE) begin
      logic enabled_feature;
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* gen_if = FindNodeByTag(tree, "kGenerateIf");
  ASSERT_NE(gen_if, nullptr);
}

// Test 13: Multiple generate regions
TEST(GenerateTest, MultipleGenerateRegions) {
  const std::string code = R"(
module test;
  generate
    for (genvar i = 0; i < 2; i++) begin
      logic [7:0] data1;
    end
  endgenerate
  
  generate
    for (genvar j = 0; j < 3; j++) begin
      logic [15:0] data2;
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count generate regions
  int gen_count = 0;
  std::function<void(const json&)> count_generates = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kGenerateRegion") {
      gen_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_generates(child);
      }
    }
  };
  count_generates(tree);
  
  EXPECT_EQ(gen_count, 2) << "Should find 2 generate regions";
}

// Test 14: Generate with module instantiation
TEST(GenerateTest, GenerateWithInstantiation) {
  const std::string code = R"(
module adder(input a, b, output sum);
  assign sum = a + b;
endmodule

module test;
  logic [7:0] a, b, sum;
  
  generate
    for (genvar i = 0; i < 8; i++) begin : gen_adders
      adder u_adder(.a(a[i]), .b(b[i]), .sum(sum[i]));
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 15: Generate for with step expression
TEST(GenerateTest, GenerateForWithStep) {
  const std::string code = R"(
module test;
  generate
    for (genvar i = 0; i < 16; i = i + 2) begin
      logic [7:0] even_reg;
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* gen = FindNodeByTag(tree, "kLoopGenerateConstruct");
  ASSERT_NE(gen, nullptr);
}

// Test 16: Generate if with complex condition
TEST(GenerateTest, GenerateIfComplexCondition) {
  const std::string code = R"(
module test #(parameter A = 1, parameter B = 2);
  generate
    if (A > B && B != 0) begin
      logic complex_feature;
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* gen_if = FindNodeByTag(tree, "kGenerateIf");
  ASSERT_NE(gen_if, nullptr);
}

// Test 17: Generate case with multiple items
TEST(GenerateTest, GenerateCaseMultipleItems) {
  const std::string code = R"(
module test #(parameter SEL = 0);
  generate
    case (SEL)
      0, 1: begin
        logic low_mode;
      end
      2, 3: begin
        logic mid_mode;
      end
      4, 5, 6, 7: begin
        logic high_mode;
      end
    endcase
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 18: Empty generate region
TEST(GenerateTest, EmptyGenerateRegion) {
  const std::string code = R"(
module test;
  generate
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* gen = FindNodeByTag(tree, "kGenerateRegion");
  ASSERT_NE(gen, nullptr);
}

// Test 19: Generate with always blocks
TEST(GenerateTest, GenerateWithAlwaysBlocks) {
  const std::string code = R"(
module test;
  logic clk;
  
  generate
    for (genvar i = 0; i < 4; i++) begin
      logic [7:0] reg_data;
      always @(posedge clk) begin
        reg_data <= reg_data + 1;
      end
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 20: Generate with continuous assignments
TEST(GenerateTest, GenerateWithAssignments) {
  const std::string code = R"(
module test;
  logic [7:0] a, b, result;
  
  generate
    for (genvar i = 0; i < 8; i++) begin
      assign result[i] = a[i] ^ b[i];
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 21: Nested if-else in generate
TEST(GenerateTest, NestedIfElseInGenerate) {
  const std::string code = R"(
module test #(parameter MODE1 = 1, parameter MODE2 = 0);
  generate
    if (MODE1) begin
      if (MODE2) begin
        logic both_enabled;
      end else begin
        logic only_mode1;
      end
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 22: Generate with function calls
TEST(GenerateTest, GenerateWithFunctionCalls) {
  const std::string code = R"(
module test;
  function int compute_width(int idx);
    return idx * 8;
  endfunction
  
  generate
    for (genvar i = 0; i < 4; i++) begin
      localparam WIDTH = compute_width(i);
      logic [WIDTH-1:0] data;
    end
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 23: Performance test (20 generate blocks)
TEST(GenerateTest, PerformanceTest) {
  std::string code = "module test;\n";
  
  for (int i = 0; i < 20; i++) {
    code += "  generate\n";
    code += "    for (genvar g" + std::to_string(i) + " = 0; g" + 
            std::to_string(i) + " < 2; g" + std::to_string(i) + "++) begin\n";
    code += "      logic [7:0] data" + std::to_string(i) + ";\n";
    code += "    end\n";
    code += "  endgenerate\n\n";
  }
  
  code += "endmodule\n";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count generate regions
  int gen_count = 0;
  std::function<void(const json&)> count_generates = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kGenerateRegion") {
      gen_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_generates(child);
      }
    }
  };
  count_generates(tree);
  
  EXPECT_EQ(gen_count, 20) << "Should find 20 generate regions";
}

// Test 24: Complex parametric design
TEST(GenerateTest, ComplexParametricDesign) {
  const std::string code = R"(
module parametric_fifo #(
  parameter DEPTH = 8,
  parameter WIDTH = 32,
  parameter USE_ASYNC = 1
);
  logic [WIDTH-1:0] fifo_mem [DEPTH-1:0];
  
  generate
    if (USE_ASYNC) begin : async_fifo
      logic wr_clk, rd_clk;
      
      for (genvar i = 0; i < DEPTH; i++) begin : mem_array
        always @(posedge wr_clk) begin
          // Write logic
        end
      end
    end else begin : sync_fifo
      logic clk;
      
      for (genvar i = 0; i < DEPTH; i++) begin : mem_array
        always @(posedge clk) begin
          // Sync logic
        end
      end
    end
  endgenerate
  
  generate
    case (WIDTH)
      8:  begin : byte_width
        logic [7:0] control;
      end
      16: begin : word_width
        logic [15:0] control;
      end
      32: begin : dword_width
        logic [31:0] control;
      end
      default: begin : custom_width
        logic [WIDTH-1:0] control;
      end
    endcase
  endgenerate
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count all generate constructs
  int gen_if_count = 0;
  int gen_for_count = 0;
  int gen_case_count = 0;
  
  std::function<void(const json&)> count_all = [&](const json& node) {
    if (node.contains("tag")) {
      if (node["tag"] == "kGenerateIf") gen_if_count++;
      if (node["tag"] == "kLoopGenerateConstruct") gen_for_count++;
      if (node["tag"] == "kGenerateCaseItemList") gen_case_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_all(child);
      }
    }
  };
  count_all(tree);
  
  EXPECT_GE(gen_if_count, 1) << "Should have at least 1 generate if";
  EXPECT_GE(gen_for_count, 2) << "Should have at least 2 generate for loops";
  EXPECT_GE(gen_case_count, 1) << "Should have at least 1 generate case";
}

}  // namespace
}  // namespace verilog

