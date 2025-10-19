// Copyright 2025 The Verible Authors.
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

// Macro Nesting Parser Tests - Phase 6
// Tests complex nested macros and code blocks as macro arguments

#include <string>

#include "gtest/gtest.h"
#include "absl/status/status.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Macro call inside macro argument
TEST(MacroNestingTest, MacroCallInArg) {
  const char* kTestCode = R"(
`define INNER(x) x + 1
`define OUTER(y) y * 2

module test;
  int result = `OUTER(`INNER(5));
endmodule
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until Phase 6 implementation
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 2: Code block (begin...end) as macro argument
TEST(MacroNestingTest, CodeBlockArg) {
  const char* kTestCode = R"(
`define EXECUTE(body) \
  initial begin \
    body \
  end

`EXECUTE(
  begin
    $display("Test");
    $display("Message");
  end
)
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until Phase 6 implementation
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 3: fork...join as macro argument
TEST(MacroNestingTest, ForkJoinArg) {
  const char* kTestCode = R"(
`define LOOP_BODY(stmt) \
  fork \
    begin \
      stmt \
    end \
  join_none

module test;
  initial begin
    `LOOP_BODY(
      fork
        $display("Parallel task");
      join
    )
  end
endmodule
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until Phase 6 implementation
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 4: foreach inside macro
TEST(MacroNestingTest, ForeachInMacro) {
  const char* kTestCode = R"(
`define ITERATE(arr, body) \
  foreach (arr[i]) begin \
    body \
  end

module test;
  int data[4];
  
  initial begin
    `ITERATE(data, $display("Item %0d", i))
  end
endmodule
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until Phase 6 implementation
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 5: Automatic variable in macro
TEST(MacroNestingTest, AutomaticVar) {
  const char* kTestCode = R"(
`define CREATE_THREAD(body) \
  fork \
    begin \
      automatic int local_var; \
      body \
    end \
  join_none

module test;
  initial begin
    `CREATE_THREAD(
      local_var = 5;
      $display("Value: %0d", local_var);
    )
  end
endmodule
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until Phase 6 implementation
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 6: Triple-level macro nesting
TEST(MacroNestingTest, TripleNesting) {
  const char* kTestCode = R"(
`define LEVEL1(x) x * 2
`define LEVEL2(y) `LEVEL1(y + 1)
`define LEVEL3(z) `LEVEL2(z - 1)

module test;
  int result = `LEVEL3(10);
endmodule
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until Phase 6 implementation
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 7: Real OpenTitan loop_ral_models pattern
TEST(MacroNestingTest, OpenTitanLoopMacro) {
  const char* kTestCode = R"(
`define loop_ral_models_to_create_threads(body) \
  fork \
    begin : isolation_fork \
      foreach (cfg.ral_models[i]) begin \
        automatic string ral_name = i; \
        fork \
          begin \
            body \
          end \
        join_none \
      end \
      wait fork; \
    end : isolation_fork \
  join

class test_seq;
  virtual task run();
    `loop_ral_models_to_create_threads(
      $display("Processing %s", ral_name)
    )
  endtask
endclass
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until Phase 6 implementation
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 8: uvm_info inside custom macro
TEST(MacroNestingTest, UVMInfoInMacro) {
  const char* kTestCode = R"(
`define LOOP_WITH_INFO(items, msg) \
  foreach (items[i]) begin \
    `uvm_info("LOOP", $sformatf(msg, i), UVM_LOW) \
  end

class test_seq extends uvm_sequence;
  int data[4];
  
  virtual task body();
    `LOOP_WITH_INFO(data, "Processing item %0d")
  endtask
endclass
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until Phase 6 implementation
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

}  // namespace
}  // namespace verilog

