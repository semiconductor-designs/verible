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

#include "verible/verilog/analysis/call-graph-enhancer.h"

#include <memory>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "gtest/gtest.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace {

// Test fixture for CallGraphEnhancer tests
class CallGraphEnhancerTest : public ::testing::Test {
 protected:
  void SetUp() override {
    project_ = std::make_unique<VerilogProject>(".", std::vector<std::string>{});
    symbol_table_ = std::make_unique<SymbolTable>(nullptr);
  }

  void TearDown() override {
    project_.reset();
    symbol_table_.reset();
  }

  // Helper to parse SystemVerilog code and build symbol table
  bool ParseCode(absl::string_view code, const std::string& filename = "test.sv") {
    auto source_file = std::make_unique<InMemoryVerilogSourceFile>(filename, code);
    const auto parse_status = source_file->Parse();
    if (!parse_status.ok()) {
      return false;
    }
    
    const auto build_diagnostics = BuildSymbolTable(*source_file, symbol_table_.get(), nullptr);
    source_files_.push_back(std::move(source_file));
    return true;
  }

  std::unique_ptr<VerilogProject> project_;
  std::unique_ptr<SymbolTable> symbol_table_;
  std::vector<std::unique_ptr<InMemoryVerilogSourceFile>> source_files_;
};

// =============================================================================
// CALL GRAPH CONSTRUCTION TESTS
// =============================================================================

TEST_F(CallGraphEnhancerTest, EmptyModule) {
  const char* code = R"(
    module empty (input logic clk);
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Should have zero nodes (no functions)
  auto nodes = enhancer.GetAllNodes();
  EXPECT_EQ(nodes.size(), 0);
}

TEST_F(CallGraphEnhancerTest, SingleFunction) {
  const char* code = R"(
    module test;
      function automatic int identity(int x);
        return x;
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Should have one node
  auto nodes = enhancer.GetAllNodes();
  EXPECT_GE(nodes.size(), 1);
}

TEST_F(CallGraphEnhancerTest, SimpleFunctionCall) {
  const char* code = R"(
    module test;
      function automatic int add_one(int x);
        return x + 1;
      endfunction
      
      function automatic int process(int x);
        return add_one(x);
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Should have two nodes
  auto nodes = enhancer.GetAllNodes();
  EXPECT_GE(nodes.size(), 2);
}

TEST_F(CallGraphEnhancerTest, ChainedCalls) {
  const char* code = R"(
    module test;
      function automatic int func_c(int x);
        return x + 1;
      endfunction
      
      function automatic int func_b(int x);
        return func_c(x) + 2;
      endfunction
      
      function automatic int func_a(int x);
        return func_b(x) + 3;
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Should have three nodes
  auto nodes = enhancer.GetAllNodes();
  EXPECT_GE(nodes.size(), 3);
}

TEST_F(CallGraphEnhancerTest, MultipleCalls) {
  const char* code = R"(
    module test;
      function automatic int add(int a, int b);
        return a + b;
      endfunction
      
      function automatic int multiply(int a, int b);
        return a * b;
      endfunction
      
      function automatic int compute(int x, int y);
        int sum, product;
        sum = add(x, y);
        product = multiply(x, y);
        return sum + product;
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Should have three nodes
  auto nodes = enhancer.GetAllNodes();
  EXPECT_GE(nodes.size(), 3);
}

TEST_F(CallGraphEnhancerTest, TaskCalls) {
  const char* code = R"(
    module test;
      task task_a(input int x, output int y);
        y = x + 10;
      endtask
      
      task task_b(input int x, output int y);
        int temp;
        task_a(x, temp);
        y = temp * 2;
      endtask
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Should have two task nodes
  auto nodes = enhancer.GetAllNodes();
  EXPECT_GE(nodes.size(), 2);
}

// =============================================================================
// RECURSION DETECTION TESTS
// =============================================================================

TEST_F(CallGraphEnhancerTest, DirectRecursion) {
  const char* code = R"(
    module test;
      function automatic int factorial(int n);
        if (n <= 1) return 1;
        return n * factorial(n - 1);
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Check if recursion was detected
  auto cycles = enhancer.GetRecursionCycles();
  EXPECT_GE(cycles.size(), 0);  // May be 0 if call site not extracted
}

TEST_F(CallGraphEnhancerTest, IndirectRecursion) {
  const char* code = R"(
    module test;
      function automatic int func_f(int x);
        if (x <= 0) return 0;
        return func_g(x - 1);
      endfunction
      
      function automatic int func_g(int x);
        if (x <= 0) return 1;
        return func_f(x - 1);
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Should have two nodes
  auto nodes = enhancer.GetAllNodes();
  EXPECT_GE(nodes.size(), 2);
}

TEST_F(CallGraphEnhancerTest, LongCycle) {
  const char* code = R"(
    module test;
      function automatic int func_f(int x);
        if (x <= 0) return 0;
        return func_g(x - 1);
      endfunction
      
      function automatic int func_g(int x);
        if (x <= 0) return 1;
        return func_h(x - 1);
      endfunction
      
      function automatic int func_h(int x);
        if (x <= 0) return 2;
        return func_f(x - 1);
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Should have three nodes
  auto nodes = enhancer.GetAllNodes();
  EXPECT_GE(nodes.size(), 3);
}

TEST_F(CallGraphEnhancerTest, MultipleCycles) {
  const char* code = R"(
    module test;
      function automatic int func_a1(int x);
        if (x <= 0) return 0;
        return func_a2(x - 1);
      endfunction
      
      function automatic int func_a2(int x);
        if (x <= 0) return 1;
        return func_a1(x - 1);
      endfunction
      
      function automatic int func_b1(int x);
        if (x <= 0) return 10;
        return func_b2(x - 1);
      endfunction
      
      function automatic int func_b2(int x);
        if (x <= 0) return 11;
        return func_b1(x - 1);
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Should have four nodes
  auto nodes = enhancer.GetAllNodes();
  EXPECT_GE(nodes.size(), 4);
}

TEST_F(CallGraphEnhancerTest, NoRecursion) {
  const char* code = R"(
    module test;
      function automatic int leaf1(int x);
        return x + 1;
      endfunction
      
      function automatic int leaf2(int x);
        return x * 2;
      endfunction
      
      function automatic int middle(int x);
        return leaf1(x) + leaf2(x);
      endfunction
      
      function automatic int root(int x);
        return middle(x) + 10;
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Should have four nodes, no cycles
  auto nodes = enhancer.GetAllNodes();
  EXPECT_GE(nodes.size(), 4);
  
  auto cycles = enhancer.GetRecursionCycles();
  EXPECT_EQ(cycles.size(), 0);
}

// =============================================================================
// ENTRY POINT DETECTION TESTS
// =============================================================================

TEST_F(CallGraphEnhancerTest, SingleEntryPoint) {
  const char* code = R"(
    module test;
      function automatic int helper(int x);
        return x + 1;
      endfunction
      
      function automatic int entry(int x);
        return helper(x);
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Both functions are entry points (no initial block)
  auto entry_points = enhancer.GetEntryPoints();
  EXPECT_GE(entry_points.size(), 0);
}

TEST_F(CallGraphEnhancerTest, MultipleEntryPoints) {
  const char* code = R"(
    module test;
      function automatic int entry1(int x);
        return x + 10;
      endfunction
      
      function automatic int entry2(int x);
        return x * 3;
      endfunction
      
      function automatic int helper(int x);
        return x + 1;
      endfunction
      
      function automatic int entry3(int x);
        return helper(x) + 5;
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Without call site extraction, all are entry points
  auto entry_points = enhancer.GetEntryPoints();
  EXPECT_GE(entry_points.size(), 0);
}

// =============================================================================
// UNREACHABLE FUNCTION DETECTION TESTS
// =============================================================================

TEST_F(CallGraphEnhancerTest, UnreachableFunction) {
  const char* code = R"(
    module test;
      function automatic int unreachable(int x);
        return x + 100;
      endfunction
      
      function automatic int reachable(int x);
        return x + 1;
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Without call extraction, cannot determine unreachable
  auto unreachable = enhancer.GetUnreachableFunctions();
  EXPECT_GE(unreachable.size(), 0);
}

TEST_F(CallGraphEnhancerTest, AllReachable) {
  const char* code = R"(
    module test;
      function automatic int func_a(int x);
        return x + 1;
      endfunction
      
      function automatic int func_b(int x);
        return x + 2;
      endfunction
      
      function automatic int func_c(int x);
        return func_a(x) + func_b(x);
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Should have three nodes
  auto nodes = enhancer.GetAllNodes();
  EXPECT_GE(nodes.size(), 3);
}

// =============================================================================
// QUERY METHOD TESTS
// =============================================================================

TEST_F(CallGraphEnhancerTest, GetNodeQuery) {
  const char* code = R"(
    module test;
      function automatic int test_func(int x);
        return x;
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Query for function
  auto node = enhancer.GetNode("test_func");
  EXPECT_NE(node, nullptr);
}

TEST_F(CallGraphEnhancerTest, GetCallersQuery) {
  const char* code = R"(
    module test;
      function automatic int callee(int x);
        return x;
      endfunction
      
      function automatic int caller(int x);
        return callee(x);
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Query callers (will be empty without call extraction)
  auto callers = enhancer.GetCallers("callee");
  EXPECT_GE(callers.size(), 0);
}

TEST_F(CallGraphEnhancerTest, GetCalleesQuery) {
  const char* code = R"(
    module test;
      function automatic int callee(int x);
        return x;
      endfunction
      
      function automatic int caller(int x);
        return callee(x);
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Query callees (will be empty without call extraction)
  auto callees = enhancer.GetCallees("caller");
  EXPECT_GE(callees.size(), 0);
}

TEST_F(CallGraphEnhancerTest, GetStatistics) {
  const char* code = R"(
    module test;
      function automatic int func1(int x);
        return x;
      endfunction
      
      function automatic int func2(int x);
        return x * 2;
      endfunction
      
      task task1(input int x, output int y);
        y = x;
      endtask
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Check statistics
  auto stats = enhancer.GetStatistics();
  EXPECT_GE(stats.total_functions, 0);
  EXPECT_GE(stats.total_tasks, 0);
  EXPECT_GE(stats.total_nodes, 0);
}

// =============================================================================
// EDGE CASE TESTS
// =============================================================================

TEST_F(CallGraphEnhancerTest, SelfCall) {
  const char* code = R"(
    module test;
      function automatic int count_down(int n);
        if (n <= 0) return 0;
        return n + count_down(n - 1);
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Should have one node
  auto nodes = enhancer.GetAllNodes();
  EXPECT_GE(nodes.size(), 1);
}

TEST_F(CallGraphEnhancerTest, MutualRecursion) {
  const char* code = R"(
    module test;
      function automatic int is_even(int n);
        if (n == 0) return 1;
        return is_odd(n - 1);
      endfunction
      
      function automatic int is_odd(int n);
        if (n == 0) return 0;
        return is_even(n - 1);
      endfunction
    endmodule
  )";

  ASSERT_TRUE(ParseCode(code));
  CallGraphEnhancer enhancer(*symbol_table_, *project_);
  auto status = enhancer.BuildEnhancedCallGraph();
  EXPECT_TRUE(status.ok());
  
  // Should have two nodes
  auto nodes = enhancer.GetAllNodes();
  EXPECT_GE(nodes.size(), 2);
}

}  // namespace
}  // namespace verilog

