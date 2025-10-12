// Copyright 2017-2020 The Verible Authors.
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

// Phase D: Dataflow Metadata Tests for Continuous Assignments
// Tests for dataflow analysis metadata in JSON export

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

// Helper: Parse module and convert to JSON
json ParseModuleToJson(const std::string& code) {
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

// Test 1: Simple assign (assign out = in)
TEST(DataflowMetadataTest, SimpleAssign) {
  const std::string code = R"(
module simple_assign;
  wire in, out;
  assign out = in;
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Find kNetVariableAssignment node with dataflow_info
  bool found_dataflow = false;
  std::function<void(const json&)> visit = [&](const json& node) {
    if (node.contains("metadata") && node["metadata"].contains("dataflow_info")) {
      const auto& df = node["metadata"]["dataflow_info"];
      EXPECT_TRUE(df.contains("has_driver"));
      EXPECT_TRUE(df["has_driver"].get<bool>());
      EXPECT_TRUE(df.contains("driver_type"));
      EXPECT_EQ(df["driver_type"].get<std::string>(), "continuous");
      EXPECT_TRUE(df.contains("target_signal"));
      // Signal should be "out" or contain "out"
      std::string target = df["target_signal"].get<std::string>();
      EXPECT_TRUE(target.find("out") != std::string::npos);
      found_dataflow = true;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        visit(child);
      }
    }
  };
  visit(tree);
  
  EXPECT_TRUE(found_dataflow) << "Should find dataflow_info metadata";
}

// Test 2: Combinational logic assign
TEST(DataflowMetadataTest, CombinationalLogic) {
  const std::string code = R"(
module comb_logic;
  wire a, b, out;
  assign out = a & b;
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  bool found_dataflow = false;
  std::function<void(const json&)> visit = [&](const json& node) {
    if (node.contains("metadata") && node["metadata"].contains("dataflow_info")) {
      const auto& df = node["metadata"]["dataflow_info"];
      EXPECT_TRUE(df["has_driver"].get<bool>());
      EXPECT_EQ(df["driver_type"].get<std::string>(), "continuous");
      found_dataflow = true;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        visit(child);
      }
    }
  };
  visit(tree);
  
  EXPECT_TRUE(found_dataflow);
}

// Test 3: Conditional assign (assign out = sel ? a : b)
TEST(DataflowMetadataTest, ConditionalAssign) {
  const std::string code = R"(
module mux;
  wire sel, a, b, out;
  assign out = sel ? a : b;
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  bool found_dataflow = false;
  std::function<void(const json&)> visit = [&](const json& node) {
    if (node.contains("metadata") && node["metadata"].contains("dataflow_info")) {
      const auto& df = node["metadata"]["dataflow_info"];
      EXPECT_TRUE(df["has_driver"].get<bool>());
      EXPECT_EQ(df["driver_type"].get<std::string>(), "continuous");
      found_dataflow = true;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        visit(child);
      }
    }
  };
  visit(tree);
  
  EXPECT_TRUE(found_dataflow);
}

// Test 4: Multiple assigns to different targets
TEST(DataflowMetadataTest, MultipleAssigns) {
  const std::string code = R"(
module multi_assign;
  wire a, b, out1, out2;
  assign out1 = a;
  assign out2 = b;
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  int dataflow_count = 0;
  std::function<void(const json&)> visit = [&](const json& node) {
    if (node.contains("metadata") && node["metadata"].contains("dataflow_info")) {
      dataflow_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        visit(child);
      }
    }
  };
  visit(tree);
  
  EXPECT_GE(dataflow_count, 2) << "Should find at least 2 dataflow metadata entries";
}

// Test 5: Bitwise operation assign
TEST(DataflowMetadataTest, BitwiseOperation) {
  const std::string code = R"(
module bitwise;
  wire [7:0] a, b, out;
  assign out = a | b;
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  bool found_dataflow = false;
  std::function<void(const json&)> visit = [&](const json& node) {
    if (node.contains("metadata") && node["metadata"].contains("dataflow_info")) {
      const auto& df = node["metadata"]["dataflow_info"];
      EXPECT_TRUE(df["has_driver"].get<bool>());
      found_dataflow = true;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        visit(child);
      }
    }
  };
  visit(tree);
  
  EXPECT_TRUE(found_dataflow);
}

// Test 6: Arithmetic operation assign
TEST(DataflowMetadataTest, ArithmeticOperation) {
  const std::string code = R"(
module arithmetic;
  wire [7:0] a, b, sum;
  assign sum = a + b;
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  bool found_dataflow = false;
  std::function<void(const json&)> visit = [&](const json& node) {
    if (node.contains("metadata") && node["metadata"].contains("dataflow_info")) {
      found_dataflow = true;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        visit(child);
      }
    }
  };
  visit(tree);
  
  EXPECT_TRUE(found_dataflow);
}

// Test 7: Concatenation assign
TEST(DataflowMetadataTest, ConcatenationAssign) {
  const std::string code = R"(
module concat;
  wire [3:0] a, b;
  wire [7:0] out;
  assign out = {a, b};
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  bool found_dataflow = false;
  std::function<void(const json&)> visit = [&](const json& node) {
    if (node.contains("metadata") && node["metadata"].contains("dataflow_info")) {
      found_dataflow = true;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        visit(child);
      }
    }
  };
  visit(tree);
  
  EXPECT_TRUE(found_dataflow);
}

// Test 8: Bus element assign
TEST(DataflowMetadataTest, BusElementAssign) {
  const std::string code = R"(
module bus_element;
  wire [7:0] bus;
  wire bit_val;
  assign bus[0] = bit_val;
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  bool found_dataflow = false;
  std::function<void(const json&)> visit = [&](const json& node) {
    if (node.contains("metadata") && node["metadata"].contains("dataflow_info")) {
      const auto& df = node["metadata"]["dataflow_info"];
      EXPECT_TRUE(df["has_driver"].get<bool>());
      found_dataflow = true;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        visit(child);
      }
    }
  };
  visit(tree);
  
  EXPECT_TRUE(found_dataflow);
}

// Test 9: Module with behavioral block and internal signal parses successfully
TEST(DataflowMetadataTest, BehavioralWithDataflow) {
  const std::string code = R"(
module mixed_dataflow;
  reg out_reg;
  wire in1, in2, internal;
  
  // Continuous assignment (should have dataflow_info)
  assign internal = in1 & in2;
  
  // Behavioral block
  always @(internal) begin
    out_reg = internal;
  end
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // This test verifies that a module with both continuous and behavioral
  // assignments parses correctly and the continuous assignment has dataflow_info
  bool found_dataflow = false;
  
  std::function<void(const json&)> visit = [&](const json& node) {
    if (node.contains("tag") && node["tag"].get<std::string>() == "kNetVariableAssignment") {
      if (node.contains("metadata") && node["metadata"].contains("dataflow_info")) {
        const auto& df = node["metadata"]["dataflow_info"];
        if (df.contains("driver_type") && df["driver_type"].get<std::string>() == "continuous") {
          found_dataflow = true;
        }
      }
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        visit(child);
      }
    }
  };
  visit(tree);
  
  // Should find continuous assignment with dataflow metadata
  EXPECT_TRUE(found_dataflow) << "Should find dataflow_info for continuous assignment in mixed module";
}

// Test 10: Complex expression assign
TEST(DataflowMetadataTest, ComplexExpression) {
  const std::string code = R"(
module complex_expr;
  wire [7:0] a, b, c;
  wire [7:0] result;
  assign result = (a + b) & c;
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  bool found_dataflow = false;
  std::function<void(const json&)> visit = [&](const json& node) {
    if (node.contains("metadata") && node["metadata"].contains("dataflow_info")) {
      const auto& df = node["metadata"]["dataflow_info"];
      EXPECT_TRUE(df["has_driver"].get<bool>());
      EXPECT_EQ(df["driver_type"].get<std::string>(), "continuous");
      found_dataflow = true;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        visit(child);
      }
    }
  };
  visit(tree);
  
  EXPECT_TRUE(found_dataflow) << "Should find dataflow for complex expression";
}

}  // namespace
}  // namespace verilog

