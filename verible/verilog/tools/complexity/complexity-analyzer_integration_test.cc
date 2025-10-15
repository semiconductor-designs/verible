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

#include "verible/verilog/tools/complexity/complexity-analyzer.h"

#include <filesystem>
#include <fstream>
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

class ComplexityAnalyzerIntegrationTest : public ::testing::Test {
 protected:
  void SetUp() override {
    test_dir_ = std::filesystem::temp_directory_path() / "verible_complexity_test";
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

// Integration Test 1: Verify ACTUAL complexity calculation with REAL CST
TEST_F(ComplexityAnalyzerIntegrationTest, ActualComplexityWithRealCST) {
  // Create a function with known complexity
  std::string test_code = R"(
module test;
  function automatic int calculate(int x);
    if (x > 10) begin
      return x * 2;
    end else if (x > 5) begin
      return x + 1;
    end else begin
      return x;
    end
  endfunction
endmodule
)";

  std::string test_file = CreateTestFile("complexity.sv", test_code);

  // Parse and build symbol table
  VerilogProject project(test_dir_.string(), std::vector<std::string>{});
  auto file_or = project.OpenTranslationUnit(test_file);
  ASSERT_TRUE(file_or.ok()) << file_or.status().message();
  ASSERT_TRUE(file_or.value()->Status().ok());

  SymbolTable symbol_table(&project);
  std::vector<absl::Status> build_diagnostics;
  symbol_table.Build(&build_diagnostics);
  ASSERT_TRUE(build_diagnostics.empty()) << "Symbol table build failed";

  // Create call graph
  analysis::CallGraph call_graph(&symbol_table);
  call_graph.Build();

  // Create analyzer WITH symbol_table
  ComplexityAnalyzer analyzer(&call_graph, &symbol_table);
  
  // Analyze
  auto report = analyzer.Analyze();

  // This is the CRITICAL TEST:
  // The function has 2 decision points (if + else if)
  // Cyclomatic complexity = decisions + 1 = 3
  // If helpers work, complexity > 1
  // If helpers DON'T work, complexity = 1 (default)

  ASSERT_FALSE(report.per_function.empty()) << "No functions found";
  
  // Get the first function's metrics
  auto& func = report.per_function.begin()->second;
  
  // DEBUG: Print actual values
  std::cout << "Function: " << func.name << "\n";
  std::cout << "  Cyclomatic complexity: " << func.cyclomatic_complexity << "\n";
  std::cout << "  Function size (LOC): " << func.function_size << "\n";
  
  // VERIFY ACTUAL COMPLEXITY CALCULATION
  // With 2 decision points (if + else if), cyclomatic complexity should be 3
  // McCabe's formula: CC = E - N + 2P where E=edges, N=nodes, P=connected components
  // Or simply: CC = decision_points + 1
  // 
  // Our function has:
  // - if (x > 10) -> decision 1
  // - else if (x > 5) -> decision 2
  // - else -> no decision (fallthrough)
  // Expected CC = 2 + 1 = 3
  
  EXPECT_GT(func.cyclomatic_complexity, 1) 
      << "Complexity is default (1) - helpers not executing!";
  
  // STRICTER TEST: Verify it's in reasonable range (2-4)
  // Could be 2 if only counting 'if', or 3 if counting 'else if'
  EXPECT_GE(func.cyclomatic_complexity, 2)
      << "Complexity too low - should be at least 2 for 2 branches";
  EXPECT_LE(func.cyclomatic_complexity, 4)
      << "Complexity too high - should be at most 4 for this simple function";
  
  // VERIFY ACTUAL LOC CALCULATION
  // Function spans lines 3-10 in the test code (8 lines including braces)
  // Exact count depends on implementation (comments? blanks? braces?)
  EXPECT_NE(func.function_size, 10)
      << "LOC is default (10) - helpers not executing!";
  
  // STRICTER TEST: Verify reasonable range (5-12 lines)
  EXPECT_GE(func.function_size, 5)
      << "LOC too low - function has at least 5 lines";
  EXPECT_LE(func.function_size, 12)
      << "LOC too high - function is only ~8 lines";
}

// Integration Test 2: Multiple functions with different complexity
TEST_F(ComplexityAnalyzerIntegrationTest, MultipleFunctions) {
  std::string test_code = R"(
module test;
  function int simple(int x);
    return x + 1;
  endfunction
  
  function int complex(int x);
    for (int i = 0; i < 10; i++) begin
      if (i > 5) begin
        x = x * 2;
      end
    end
    return x;
  endfunction
endmodule
)";

  std::string test_file = CreateTestFile("multi.sv", test_code);

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

  ComplexityAnalyzer analyzer(&call_graph, &symbol_table);
  auto report = analyzer.Analyze();

  // Should find both functions
  EXPECT_GE(report.total_functions, 2);
  
  // Verify NOT all default values
  bool found_non_default_complexity = false;
  bool found_non_default_size = false;
  
  for (const auto& pair : report.per_function) {
    const auto& func = pair.second;
    if (func.cyclomatic_complexity != 1) found_non_default_complexity = true;
    if (func.function_size != 10) found_non_default_size = true;
  }
  
  EXPECT_TRUE(found_non_default_complexity) << "All complexities are default!";
  EXPECT_TRUE(found_non_default_size) << "All sizes are default!";
}

}  // namespace
}  // namespace tools
}  // namespace verilog
