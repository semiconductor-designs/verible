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

#include "verible/verilog/tools/deadcode/dead-code-eliminator.h"

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "verible/verilog/analysis/call-graph.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace tools {
namespace {

using ::testing::Contains;

class DeadCodeEliminatorIntegrationTest : public ::testing::Test {
 protected:
  void SetUp() override {
    test_dir_ = std::filesystem::temp_directory_path() / "verible_deadcode_test";
    std::filesystem::create_directories(test_dir_);
  }

  void TearDown() override {
    if (std::filesystem::exists(test_dir_)) {
      std::filesystem::remove_all(test_dir_);
    }
  }

  std::string CreateTestFile(const std::string& filename, const std::string& content) {
    auto filepath = test_dir_ / filename;
    std::ofstream file(filepath);
    file << content;
    file.close();
    return filepath.string();
  }

  std::filesystem::path test_dir_;
};

// Integration Test 1: Verify Dead Code Detection with Real Parsed Files
TEST_F(DeadCodeEliminatorIntegrationTest, DetectDeadFunctionWithRealCST) {
  // Create module with one used function and one unused function
  std::string test_code = R"(
module test;
  initial begin
    used_function();
  end
  
  function automatic void used_function();
    // This is called
  endfunction
  
  function automatic void unused_function();
    // This is NEVER called - should be detected as dead!
  endfunction
endmodule
)";

  std::string test_file = CreateTestFile("deadcode.sv", test_code);

  // Parse and build symbol table
  VerilogProject project(test_dir_.string(), std::vector<std::string>{});
  auto file_or = project.OpenTranslationUnit(test_file);
  ASSERT_TRUE(file_or.ok()) << file_or.status().message();
  ASSERT_TRUE(file_or.value()->Status().ok());

  SymbolTable symbol_table(&project);
  std::vector<absl::Status> build_diagnostics;
  symbol_table.Build(&build_diagnostics);
  ASSERT_TRUE(build_diagnostics.empty()) << "Symbol table build failed";

  // Build call graph
  analysis::CallGraph call_graph(&symbol_table);
  call_graph.Build();

  // DEBUG: Check call graph state
  auto metrics = call_graph.GetMetrics();
  std::cout << "DEBUG: Call graph has " << metrics.node_count << " nodes, " 
            << metrics.edge_count << " edges\n";

  // Create eliminator
  DeadCodeEliminator eliminator(&call_graph, &symbol_table);
  
  // Find dead code
  auto report = eliminator.FindDeadCode();

  // DEBUG: Print report details
  std::cout << "DEBUG: Dead code report:\n";
  std::cout << "  Total dead: " << report.total_dead_count << "\n";
  std::cout << "  Dead functions: " << report.dead_functions.size() << "\n";
  for (const auto& name : report.dead_functions) {
    std::cout << "    - " << name << "\n";
  }
  std::cout << "  Summary: " << report.summary << "\n";

  // PHASE 5 PERFECTION: CallGraph now extracts calls from initial blocks! ✅
  // CallGraph has 3 nodes (2 functions + $module_scope) and 1+ edges
  // This means CallGraph::Build() NOW extracts calls from 'initial' blocks!
  
  EXPECT_GE(metrics.edge_count, 1) 
      << "CallGraph now finds edges from initial blocks!";
  
  // With edges, FindDeadCode should now find unused_function as dead
  EXPECT_EQ(report.total_dead_count, 1)
      << "Should detect unused_function as dead code";
  
  EXPECT_EQ(report.dead_functions.size(), 1)
      << "Should find 1 dead function";
  
  if (!report.dead_functions.empty()) {
    EXPECT_EQ(*report.dead_functions.begin(), "unused_function")
        << "The dead function should be unused_function";
  }
}

// Integration Test 2: No False Positives (Used Functions Not Marked Dead)
TEST_F(DeadCodeEliminatorIntegrationTest, NoFalsePositives) {
  std::string test_code = R"(
module test;
  initial begin
    func_a();
  end
  
  function automatic void func_a();
    func_b();
  endfunction
  
  function automatic void func_b();
    // Called by func_a
  endfunction
endmodule
)";

  std::string test_file = CreateTestFile("no_dead.sv", test_code);

  VerilogProject project(test_dir_.string(), std::vector<std::string>{});
  auto file_or = project.OpenTranslationUnit(test_file);
  ASSERT_TRUE(file_or.ok());
  ASSERT_TRUE(file_or.value()->Status().ok());

  SymbolTable symbol_table(&project);
  std::vector<absl::Status> build_diagnostics;
  symbol_table.Build(&build_diagnostics);
  ASSERT_TRUE(build_diagnostics.empty());

  analysis::CallGraph call_graph(&symbol_table);
  call_graph.Build();

  DeadCodeEliminator eliminator(&call_graph, &symbol_table);
  auto report = eliminator.FindDeadCode();

  // All functions are used - should find NO dead code
  EXPECT_EQ(report.total_dead_count, 0)
      << "False positives: marked used functions as dead!";
}

// Integration Test 3: Multiple Dead Functions
TEST_F(DeadCodeEliminatorIntegrationTest, MultipleDeadFunctions) {
  std::string test_code = R"(
module test;
  initial begin
    only_used();
  end
  
  function void only_used();
  endfunction
  
  function void dead_1();
  endfunction
  
  function void dead_2();
  endfunction
  
  function void dead_3();
  endfunction
endmodule
)";

  std::string test_file = CreateTestFile("multi_dead.sv", test_code);

  VerilogProject project(test_dir_.string(), std::vector<std::string>{});
  auto file_or = project.OpenTranslationUnit(test_file);
  ASSERT_TRUE(file_or.ok());
  ASSERT_TRUE(file_or.value()->Status().ok());

  SymbolTable symbol_table(&project);
  std::vector<absl::Status> build_diagnostics;
  symbol_table.Build(&build_diagnostics);
  ASSERT_TRUE(build_diagnostics.empty());

  analysis::CallGraph call_graph(&symbol_table);
  call_graph.Build();

  DeadCodeEliminator eliminator(&call_graph, &symbol_table);
  auto report = eliminator.FindDeadCode();

  // PHASE 5 PERFECTION: CallGraph now works!
  auto metrics = call_graph.GetMetrics();
  
  std::cout << "DEBUG Test3: nodes=" << metrics.node_count 
            << " edges=" << metrics.edge_count 
            << " dead=" << report.total_dead_count << "\n";
  
  // CallGraph now has edges
  EXPECT_GE(metrics.edge_count, 1) << "CallGraph now finds edges!";
  
  // Should detect 3 dead functions (dead_1, dead_2, dead_3)
  EXPECT_EQ(report.total_dead_count, 3) << "Should find 3 dead functions";
  EXPECT_EQ(report.dead_functions.size(), 3);
}

}  // namespace
}  // namespace tools
}  // namespace verilog
