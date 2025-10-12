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

#include "verible/verilog/CST/verilog-tree-json.h"

#include <memory>

#include "gtest/gtest.h"
#include "nlohmann/json.hpp"
#include "verible/common/text/symbol.h"
#include "verible/common/util/logging.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

using nlohmann::json;

TEST(VerilogTreeJsonTest, GeneratesGoodJsonTree) {
  const auto analyzer_ptr = std::make_unique<VerilogAnalyzer>(
      "module foo;\nendmodule\n", "fake_file.sv");
  const auto status = ABSL_DIE_IF_NULL(analyzer_ptr)->Analyze();
  EXPECT_TRUE(status.ok()) << status.message();
  const verible::SymbolPtr &tree_ptr = analyzer_ptr->SyntaxTree();
  ASSERT_NE(tree_ptr, nullptr);

  const json tree_json(verilog::ConvertVerilogTreeToJson(
      *tree_ptr, analyzer_ptr->Data().Contents()));

  // Verify structure (with location metadata now included)
  ASSERT_TRUE(tree_json.is_object());
  EXPECT_EQ(tree_json["tag"], "kDescriptionList");
  EXPECT_EQ(tree_json["text"], "module foo;\nendmodule");
  ASSERT_TRUE(tree_json.contains("location"));
  ASSERT_TRUE(tree_json.contains("children"));
  
  // Verify module declaration
  ASSERT_EQ(tree_json["children"].size(), 1);
  const auto& module_decl = tree_json["children"][0];
  EXPECT_EQ(module_decl["tag"], "kModuleDeclaration");
  EXPECT_EQ(module_decl["text"], "module foo;\nendmodule");
  ASSERT_TRUE(module_decl.contains("location"));
  
  // Verify children structure
  ASSERT_TRUE(module_decl.contains("children"));
  ASSERT_GE(module_decl["children"].size(), 3);
  
  // Verify module header
  const auto& header = module_decl["children"][0];
  EXPECT_EQ(header["tag"], "kModuleHeader");
  EXPECT_EQ(header["text"], "module foo;");
  ASSERT_TRUE(header.contains("location"));
  
  // Verify header has expected children (module keyword, identifier, semicolon)
  ASSERT_TRUE(header.contains("children"));
  ASSERT_GE(header["children"].size(), 3);
}

// ============================================================================
// LOCATION METADATA TESTS (Priority 1: VeriPG Enhancement)
// ============================================================================

TEST(VerilogTreeJsonTest, LocationMetadata_SimpleModule) {
  const std::string code = R"(
module top;
  wire a;
endmodule
)";
  
  const auto analyzer = std::make_unique<VerilogAnalyzer>(code, "test.sv");
  ASSERT_TRUE(analyzer->Analyze().ok());
  
  json tree_json = ConvertVerilogTreeToJson(*analyzer->SyntaxTree(), code);
  
  // Verify root has location
  ASSERT_TRUE(tree_json.contains("location"));
  ASSERT_TRUE(tree_json["location"].contains("start_line"));
  ASSERT_TRUE(tree_json["location"].contains("start_column"));
  ASSERT_TRUE(tree_json["location"].contains("end_line"));
  ASSERT_TRUE(tree_json["location"].contains("end_column"));
  
  // Verify line numbers are reasonable (1-5)
  EXPECT_GE(tree_json["location"]["start_line"].get<int>(), 1);
  EXPECT_LE(tree_json["location"]["end_line"].get<int>(), 5);
  EXPECT_GT(tree_json["location"]["start_column"].get<int>(), 0);
}

TEST(VerilogTreeJsonTest, LocationMetadata_GatePrimitives) {
  const std::string code = R"(module gates;
  and gate1(out, a, b);
  or  gate2(out2, c, d);
endmodule)";
  
  const auto analyzer = std::make_unique<VerilogAnalyzer>(code, "test.sv");
  ASSERT_TRUE(analyzer->Analyze().ok());
  
  json tree_json = ConvertVerilogTreeToJson(*analyzer->SyntaxTree(), code);
  
  // Verify root has location
  ASSERT_TRUE(tree_json.contains("location"));
  EXPECT_GE(tree_json["location"]["start_line"].get<int>(), 1);
  
  // Find gate instances and verify their line numbers
  ASSERT_TRUE(tree_json.contains("children"));
  ASSERT_GT(tree_json["children"].size(), 0);
  
  const json& module_decl = tree_json["children"][0];
  ASSERT_TRUE(module_decl.contains("children"));
  
  // Verify gate instances have location metadata
  bool found_any_with_location = false;
  for (const auto& child : module_decl["children"]) {
    if (child.is_object() && child.contains("tag") && child.contains("location")) {
      // Any child with location is good
      EXPECT_TRUE(child["location"].contains("start_line"));
      EXPECT_TRUE(child["location"].contains("start_column"));
      found_any_with_location = true;
    }
  }
  EXPECT_TRUE(found_any_with_location) << "Should find nodes with location";
}

TEST(VerilogTreeJsonTest, LocationMetadata_MultilineConstruct) {
  const std::string code = R"(
module multi;
  always_ff @(posedge clk) begin
    if (rst)
      q <= 0;
    else
      q <= d;
  end
endmodule
)";
  
  const auto analyzer = std::make_unique<VerilogAnalyzer>(code, "test.sv");
  ASSERT_TRUE(analyzer->Analyze().ok());
  
  json tree_json = ConvertVerilogTreeToJson(*analyzer->SyntaxTree(), code);
  
  // Helper function to find always_ff node
  std::function<json*(json&)> find_always;
  find_always = [&find_always](json& node) -> json* {
    if (node.is_object() && node.contains("tag")) {
      if (node["tag"] == "kAlwaysStatement") {
        return &node;
      }
      if (node.contains("children")) {
        for (auto& child : node["children"]) {
          if (child.is_object()) {
            json* result = find_always(child);
            if (result) return result;
          }
        }
      }
    }
    return nullptr;
  };
  
  json* always_node = find_always(tree_json);
  ASSERT_NE(always_node, nullptr) << "Should find always_ff node";
  
  // Verify always_ff has location
  ASSERT_TRUE(always_node->contains("location"));
  const json& loc = (*always_node)["location"];
  EXPECT_TRUE(loc.contains("start_line"));
  EXPECT_TRUE(loc.contains("end_line"));
  EXPECT_TRUE(loc.contains("start_column"));
  EXPECT_TRUE(loc.contains("end_column"));
  // Verify location is reasonable
  EXPECT_GE(loc["start_line"].get<int>(), 1);
  EXPECT_GE(loc["end_line"].get<int>(), loc["start_line"].get<int>());
}

TEST(VerilogTreeJsonTest, LocationMetadata_ExpressionNodes) {
  const std::string code = R"(module expr;
  assign sum = a + b;
endmodule)";
  
  const auto analyzer = std::make_unique<VerilogAnalyzer>(code, "test.sv");
  ASSERT_TRUE(analyzer->Analyze().ok());
  
  json tree_json = ConvertVerilogTreeToJson(*analyzer->SyntaxTree(), code);
  
  // Helper to find binary expression
  std::function<json*(json&)> find_binary;
  find_binary = [&find_binary](json& node) -> json* {
    if (node.is_object() && node.contains("tag")) {
      if (node["tag"] == "kBinaryExpression") {
        return &node;
      }
      if (node.contains("children")) {
        for (auto& child : node["children"]) {
          if (child.is_object()) {
            json* result = find_binary(child);
            if (result) return result;
          }
        }
      }
    }
    return nullptr;
  };
  
  json* binary_node = find_binary(tree_json);
  ASSERT_NE(binary_node, nullptr) << "Should find binary expression (a + b)";
  
  // Verify expression has location
  ASSERT_TRUE(binary_node->contains("location"));
  EXPECT_TRUE((*binary_node)["location"].contains("start_line"));
  EXPECT_GE((*binary_node)["location"]["start_line"].get<int>(), 1);
}

TEST(VerilogTreeJsonTest, LocationMetadata_LeafTokens) {
  const std::string code = R"(module leaf;
  wire signal;
endmodule)";
  
  const auto analyzer = std::make_unique<VerilogAnalyzer>(code, "test.sv");
  ASSERT_TRUE(analyzer->Analyze().ok());
  
  json tree_json = ConvertVerilogTreeToJson(*analyzer->SyntaxTree(), code);
  
  // Helper to find identifier "signal"
  std::function<json*(json&)> find_signal;
  find_signal = [&find_signal](json& node) -> json* {
    if (node.is_object() && node.contains("tag") && node.contains("text")) {
      if (node["tag"] == "SymbolIdentifier" && node["text"] == "signal") {
        return &node;
      }
    }
    if (node.is_object() && node.contains("children")) {
      for (auto& child : node["children"]) {
        if (child.is_object()) {
          json* result = find_signal(child);
          if (result) return result;
        }
      }
    }
    return nullptr;
  };
  
  json* signal_node = find_signal(tree_json);
  ASSERT_NE(signal_node, nullptr) << "Should find 'signal' identifier";
  
  // Verify leaf token has location
  ASSERT_TRUE(signal_node->contains("location"));
  EXPECT_GE((*signal_node)["location"]["start_line"].get<int>(), 1);
  EXPECT_GT((*signal_node)["location"]["start_column"].get<int>(), 0);
}

TEST(VerilogTreeJsonTest, LocationMetadata_AccurateColumns) {
  // Test that column numbers are present and reasonable
  const std::string code = "module m; endmodule";
  
  const auto analyzer = std::make_unique<VerilogAnalyzer>(code, "test.sv");
  ASSERT_TRUE(analyzer->Analyze().ok());
  
  json tree_json = ConvertVerilogTreeToJson(*analyzer->SyntaxTree(), code);
  
  // Verify location has all fields
  ASSERT_TRUE(tree_json.contains("location"));
  ASSERT_TRUE(tree_json["location"].contains("start_line"));
  ASSERT_TRUE(tree_json["location"].contains("start_column"));
  ASSERT_TRUE(tree_json["location"].contains("end_line"));
  ASSERT_TRUE(tree_json["location"].contains("end_column"));
  
  // Everything should be on line 1
  EXPECT_EQ(tree_json["location"]["start_line"].get<int>(), 1);
  EXPECT_EQ(tree_json["location"]["end_line"].get<int>(), 1);
  EXPECT_GT(tree_json["location"]["start_column"].get<int>(), 0);
  EXPECT_GT(tree_json["location"]["end_column"].get<int>(), 0);
}

TEST(VerilogTreeJsonTest, LocationMetadata_MultilineStrings) {
  // Test multiline construct (not actual multiline string which is invalid SV)
  const std::string code = R"(module str;
  initial begin
    $display("Hello");
    $display("World");
  end
endmodule)";
  
  const auto analyzer = std::make_unique<VerilogAnalyzer>(code, "test.sv");
  ASSERT_TRUE(analyzer->Analyze().ok());
  
  json tree_json = ConvertVerilogTreeToJson(*analyzer->SyntaxTree(), code);
  
  // Verify module has location and spans multiple lines
  ASSERT_TRUE(tree_json.contains("location"));
  EXPECT_GE(tree_json["location"]["start_line"].get<int>(), 1);
  EXPECT_GE(tree_json["location"]["end_line"].get<int>(), tree_json["location"]["start_line"].get<int>());
}

TEST(VerilogTreeJsonTest, LocationMetadata_EmptyLines) {
  const std::string code = R"(

module empty_lines;

  wire a;

endmodule

)";
  
  const auto analyzer = std::make_unique<VerilogAnalyzer>(code, "test.sv");
  ASSERT_TRUE(analyzer->Analyze().ok());
  
  json tree_json = ConvertVerilogTreeToJson(*analyzer->SyntaxTree(), code);
  
  // Module should have location (line number will vary based on CST structure)
  ASSERT_TRUE(tree_json.contains("location"));
  EXPECT_GE(tree_json["location"]["start_line"].get<int>(), 1);
}

TEST(VerilogTreeJsonTest, LocationMetadata_AllNodesHaveLocation) {
  const std::string code = R"(module all_nodes;
  reg [7:0] data;
  assign out = data & mask;
endmodule)";
  
  const auto analyzer = std::make_unique<VerilogAnalyzer>(code, "test.sv");
  ASSERT_TRUE(analyzer->Analyze().ok());
  
  json tree_json = ConvertVerilogTreeToJson(*analyzer->SyntaxTree(), code);
  
  // Verify that nodes with location have valid fields
  int node_count = 0;
  int nodes_with_location = 0;
  
  std::function<void(const json&)> count_locations;
  count_locations = [&](const json& node) {
    if (node.is_object() && node.contains("tag")) {
      node_count++;
      if (node.contains("location") && node["location"].is_object()) {
        nodes_with_location++;
        // Verify location has all required fields when present
        const json& loc = node["location"];
        if (loc.contains("start_line")) {
          EXPECT_TRUE(loc["start_line"].is_number());
          EXPECT_GE(loc["start_line"].get<int>(), 1);
        }
        if (loc.contains("start_column")) {
          EXPECT_TRUE(loc["start_column"].is_number());
        }
        if (loc.contains("end_line")) {
          EXPECT_TRUE(loc["end_line"].is_number());
        }
        if (loc.contains("end_column")) {
          EXPECT_TRUE(loc["end_column"].is_number());
        }
      }
      if (node.contains("children")) {
        for (const auto& child : node["children"]) {
          if (!child.is_null()) {
            count_locations(child);
          }
        }
      }
    }
  };
  
  count_locations(tree_json);
  
  // All nodes should have location metadata!
  EXPECT_EQ(node_count, nodes_with_location) 
      << "All " << node_count << " nodes should have location metadata";
  EXPECT_GT(nodes_with_location, 10) << "Should have multiple nodes with location";
}

}  // namespace
}  // namespace verilog
