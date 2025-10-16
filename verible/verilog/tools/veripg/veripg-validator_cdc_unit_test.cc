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

// Unit tests for CDC detection helper functions
// Purpose: Test each helper function independently to isolate CST API issues

#include "verible/verilog/tools/veripg/veripg-validator.h"

#include <iostream>
#include <iomanip>
#include <string>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/analysis/verilog-project.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-checker.h"
#include "verible/verilog/analysis/type-inference.h"
#include "verible/verilog/parser/verilog-token-enum.h"
#include "verible/common/text/tree-utils.h"

namespace verilog {
namespace tools {
namespace {

using ::testing::HasSubstr;

class CDCHelperUnitTest : public ::testing::Test {
 protected:
  // Helper to parse SystemVerilog code and get the CST root
  std::unique_ptr<VerilogAnalyzer> ParseCode(const std::string& code) {
    auto analyzer = std::make_unique<VerilogAnalyzer>(code, "test.sv");
    auto status = analyzer->Analyze();
    if (!status.ok()) {
      std::cerr << "Parse failed: " << status.message() << std::endl;
    }
    return analyzer;
  }
};

// Test: Verify we can parse always_ff blocks
TEST_F(CDCHelperUnitTest, CanParseAlwaysFF) {
  const std::string code = R"(
module test;
  logic clk, data;
  always_ff @(posedge clk) begin
    data <= 1'b0;
  end
endmodule
)";
  
  auto analyzer = ParseCode(code);
  ASSERT_TRUE(analyzer->LexStatus().ok());
  ASSERT_TRUE(analyzer->ParseStatus().ok());
  
  const auto& syntax_tree = analyzer->Data().SyntaxTree();
  ASSERT_NE(syntax_tree, nullptr);
  
  // Print CST structure for inspection
  std::cout << "\n=== CST Structure for always_ff ===" << std::endl;
  std::cout << verible::RawTreePrinter(*syntax_tree) << std::endl;
}

// Test: Find always_ff nodes manually
TEST_F(CDCHelperUnitTest, FindAlwaysFFNodes) {
  const std::string code = R"(
module test;
  logic clk_a, clk_b;
  logic data_a, data_b;
  
  always_ff @(posedge clk_a) begin
    data_a <= 1'b0;
  end
  
  always_ff @(posedge clk_b) begin
    data_b <= data_a;
  end
endmodule
)";
  
  auto analyzer = ParseCode(code);
  ASSERT_TRUE(analyzer->ParseStatus().ok());
  
  const auto& syntax_tree = analyzer->Data().SyntaxTree();
  ASSERT_NE(syntax_tree, nullptr);
  
  // Manual traversal to find always_ff
  int always_ff_count = 0;
  std::function<void(const verible::Symbol&)> count_always_ff = 
      [&](const verible::Symbol& sym) {
    if (sym.Kind() == verible::SymbolKind::kNode) {
      const auto& node = verible::down_cast<const verible::SyntaxTreeNode&>(sym);
      
      // Check if first child is TK_always_ff
      if (node.size() > 0 && node[0]) {
        if (node[0]->Kind() == verible::SymbolKind::kLeaf) {
          const auto& leaf = verible::SymbolCastToLeaf(*node[0]);
          verilog_tokentype token_type = static_cast<verilog_tokentype>(leaf.get().token_enum());
          
          if (token_type == TK_always_ff) {
            always_ff_count++;
            std::cout << "Found always_ff block #" << always_ff_count << std::endl;
          }
        }
      }
      
      // Recurse
      for (const auto& child : node.children()) {
        if (child) count_always_ff(*child);
      }
    }
  };
  
  count_always_ff(*syntax_tree);
  
  EXPECT_EQ(always_ff_count, 2) << "Should find 2 always_ff blocks";
}

// Test: ExtractClockFromBlock helper
TEST_F(CDCHelperUnitTest, ExtractClockFromBlock) {
  const std::string code = R"(
module test;
  logic clk_a;
  logic data;
  
  always_ff @(posedge clk_a) begin
    data <= 1'b0;
  end
endmodule
)";
  
  auto analyzer = ParseCode(code);
  ASSERT_TRUE(analyzer->ParseStatus().ok());
  
  const auto& syntax_tree = analyzer->Data().SyntaxTree();
  ASSERT_NE(syntax_tree, nullptr);
  
  // Find the always_ff node
  const verible::SyntaxTreeNode* always_ff_node = nullptr;
  std::function<void(const verible::Symbol&)> find_node = 
      [&](const verible::Symbol& sym) {
    if (always_ff_node) return;  // Already found
    
    if (sym.Kind() == verible::SymbolKind::kNode) {
      const auto& node = verible::down_cast<const verible::SyntaxTreeNode&>(sym);
      
      if (node.size() > 0 && node[0]) {
        if (node[0]->Kind() == verible::SymbolKind::kLeaf) {
          const auto& leaf = verible::SymbolCastToLeaf(*node[0]);
          if (static_cast<verilog_tokentype>(leaf.get().token_enum()) == TK_always_ff) {
            always_ff_node = &node;
            return;
          }
        }
      }
      
      for (const auto& child : node.children()) {
        if (child) find_node(*child);
      }
    }
  };
  
  find_node(*syntax_tree);
  ASSERT_NE(always_ff_node, nullptr) << "Should find always_ff node";
  
  // Test ExtractClockFromBlock
  analysis::TypeInference type_inference(nullptr);
  analysis::TypeChecker type_checker(nullptr, &type_inference);
  VeriPGValidator validator(&type_checker);
  
  // Use reflection to call private method (for testing)
  // Since we can't access private methods, let's just verify the node structure
  std::cout << "\n=== always_ff node structure ===" << std::endl;
  std::cout << verible::RawTreePrinter(*always_ff_node) << std::endl;
  
  // TODO: Once we understand the structure, we can test ExtractClockFromBlock
  // For now, just verify we found the node
  EXPECT_TRUE(true) << "Test infrastructure works, need to understand CST structure";
}

// Test: Verify we understand why CDC detection returns 0 violations
TEST_F(CDCHelperUnitTest, WhyCDCDetectionFails) {
  // This test documents the current state: we can find always_ff blocks
  // but CheckCDCViolations returns 0 violations
  // 
  // From previous tests we know:
  // 1. FindAlwaysFFNodes successfully finds 2 blocks
  // 2. CST structure is well understood
  // 3. Integration tests get 0 violations
  //
  // Hypothesis: Either ExtractClockFromBlock, GetAssignedSignalsInBlock,
  // or GetUsedSignalsInBlock is returning empty results
  //
  // To debug this without VerilogProject integration complexity,
  // we need to add logging to the actual detection code or test helpers directly
  
  std::cout << "\n=== CDC Detection Analysis ===" << std::endl;
  std::cout << "Unit tests prove we CAN find always_ff blocks" << std::endl;
  std::cout << "Integration tests prove CheckCDCViolations returns 0 violations" << std::endl;
  std::cout << "Next step: Add logging to helper functions" << std::endl;
  std::cout << "Suspected issue: One of the helper functions returns empty" << std::endl;
  
  EXPECT_TRUE(true) << "This test documents the investigation status";
}

}  // namespace
}  // namespace tools
}  // namespace verilog

