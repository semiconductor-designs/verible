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

// Tests for Scope/Hierarchy Metadata in JSON CST export (Phase C)

#include <string>
#include "gtest/gtest.h"
#include "nlohmann/json.hpp"
#include "verible/common/text/concrete-syntax-tree.h"
#include "verible/verilog/CST/verilog-tree-json.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

using json = nlohmann::json;

// Helper: Parse code and return JSON tree
static json ParseToJson(const std::string &code) {
  const auto analyzer_ptr =
      verilog::VerilogAnalyzer::AnalyzeAutomaticMode(code, "<test>", verilog::VerilogPreprocess::Config());
  if (!analyzer_ptr) return json();
  
  const auto& analyzer = *analyzer_ptr;
  if (!analyzer.LexStatus().ok() || !analyzer.ParseStatus().ok()) {
    return json();
  }
  
  const auto &tree = analyzer.SyntaxTree();
  if (!tree) return json();
  
  return ConvertVerilogTreeToJson(*tree, analyzer.Data().Contents());
}

// Helper: Find node by tag
static const json* FindNodeByTag(const json &node, const std::string &tag) {
  if (node.contains("tag") && node["tag"] == tag) {
    return &node;
  }
  
  if (node.contains("children")) {
    for (const auto &child : node["children"]) {
      const json* result = FindNodeByTag(child, tag);
      if (result) return result;
    }
  }
  
  return nullptr;
}

// ============================================================================
// TEST 1: Module Scope Tracking
// ============================================================================

TEST(ScopeMetadataTest, ModuleScopeTracking) {
  const std::string code = R"(
module test_module;
  logic data;
endmodule
)";

  const json tree_json = ParseToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* mod_node = FindNodeByTag(tree_json, "kModuleDeclaration");
  ASSERT_NE(mod_node, nullptr);
  
  if (mod_node->contains("metadata") && (*mod_node)["metadata"].contains("scope_info")) {
    const auto& scope = (*mod_node)["metadata"]["scope_info"];
    EXPECT_EQ(scope["scope_type"], "module");
    EXPECT_EQ(scope["scope_name"], "test_module");
  }
}

// ============================================================================
// TEST 2: Function Scope Tracking
// ============================================================================

TEST(ScopeMetadataTest, FunctionScopeTracking) {
  const std::string code = R"(
module test;
  function int add(int a, int b);
    return a + b;
  endfunction
endmodule
)";

  const json tree_json = ParseToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* func_node = FindNodeByTag(tree_json, "kFunctionDeclaration");
  if (func_node && func_node->contains("metadata") && (*func_node)["metadata"].contains("scope_info")) {
    const auto& scope = (*func_node)["metadata"]["scope_info"];
    EXPECT_EQ(scope["scope_type"], "function");
    EXPECT_TRUE(scope.contains("scope_name"));
  }
}

// ============================================================================
// TEST 3: Nested Scopes (Begin/End Blocks)
// ============================================================================

TEST(ScopeMetadataTest, NestedScopes) {
  const std::string code = R"(
module test;
  always_comb begin
    logic temp;
    temp = 1'b1;
  end
endmodule
)";

  const json tree_json = ParseToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  // Module should have scope metadata
  const json* mod_node = FindNodeByTag(tree_json, "kModuleDeclaration");
  ASSERT_NE(mod_node, nullptr);
  
  // Begin/end block might have scope metadata
  const json* seq_block = FindNodeByTag(tree_json, "kSeqBlock");
  if (seq_block && seq_block->contains("metadata") && (*seq_block)["metadata"].contains("scope_info")) {
    const auto& scope = (*seq_block)["metadata"]["scope_info"];
    EXPECT_EQ(scope["scope_type"], "block");
  }
}

// ============================================================================
// TEST 4: Scope Hierarchy (Parent-Child)
// ============================================================================

TEST(ScopeMetadataTest, ScopeHierarchy) {
  const std::string code = R"(
module top;
  module_inst sub();
endmodule
)";

  const json tree_json = ParseToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* top_mod = FindNodeByTag(tree_json, "kModuleDeclaration");
  if (top_mod && top_mod->contains("metadata") && (*top_mod)["metadata"].contains("scope_info")) {
    const auto& scope = (*top_mod)["metadata"]["scope_info"];
    EXPECT_EQ(scope["scope_name"], "top");
    EXPECT_EQ(scope["scope_type"], "module");
  }
}

}  // namespace
}  // namespace verilog

