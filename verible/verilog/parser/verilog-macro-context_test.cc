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

// Unit tests for macro-aware context tracking (v5.6.0)
// Tests macro boundary markers and context preservation

#include <string>

#include "gtest/gtest.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Simple Macro Boundary Markers Recognition
// Tests that lexer recognizes <MACRO_START> and <MACRO_END> tokens
TEST(MacroContextTest, SimpleMacroBoundaryMarkers) {
  const std::string code = R"(
    module test;
      <MACRO_START>
      logic a;
      <MACRO_END>
    endmodule
  )";
  
  VerilogAnalyzer analyzer(code, "test.sv");
  auto status = analyzer.Analyze();
  
  // Should lex without errors
  EXPECT_TRUE(status.ok()) 
    << "Macro boundary markers should be recognized by lexer";
}

// Test 2: Event Trigger After Macro With Markers
// Tests that context is preserved through macro expansion
TEST(MacroContextTest, EventTriggerAfterMacroWithMarkers) {
  const std::string code = R"(
    `define LOG(msg) $display(msg)
    
    class test;
      event my_event;
      
      task run();
        <MACRO_START>
        $display("message");
        <MACRO_END>
        -> my_event;
      endtask
    endclass
  )";
  
  VerilogAnalyzer analyzer(code, "test.sv");
  auto status = analyzer.Analyze();
  
  EXPECT_TRUE(status.ok()) 
    << "Event trigger after macro with markers should parse successfully";
}

// Test 3: Nested Macro Context Preservation
// Tests that nested macros preserve context correctly
TEST(MacroContextTest, NestedMacroContextPreservation) {
  const std::string code = R"(
    `define OUTER(x) `INNER(x) + 1
    `define INNER(y) y * 2
    
    module test;
      event e;
      task test_task();
        <MACRO_START>
        $display("outer");
        <MACRO_START>
        $display("inner");
        <MACRO_END>
        -> e;
        <MACRO_END>
      endtask
    endmodule
  )";
  
  VerilogAnalyzer analyzer(code, "test.sv");
  auto status = analyzer.Analyze();
  
  EXPECT_TRUE(status.ok()) 
    << "Nested macros with markers should preserve context";
}

// Test 4: Logical Implication Still Works
// Tests that expressions with -> still work correctly
TEST(MacroContextTest, LogicalImplicationStillWorks) {
  const std::string code = R"(
    module test;
      logic a, b, result;
      
      always_comb begin
        <MACRO_START>
        result = (a -> b);
        <MACRO_END>
      end
    endmodule
  )";
  
  VerilogAnalyzer analyzer(code, "test.sv");
  auto status = analyzer.Analyze();
  
  EXPECT_TRUE(status.ok()) 
    << "Logical implication in expression should still work with markers";
}

// Test 5: Unbalanced Markers Graceful Handling
// Tests that parser doesn't crash on unbalanced markers
TEST(MacroContextTest, UnbalancedMarkersGraceful) {
  const std::string code = R"(
    module test;
      task test_task();
        <MACRO_START>
        logic a;
        // Missing MACRO_END - should handle gracefully
      endtask
    endmodule
  )";
  
  VerilogAnalyzer analyzer(code, "test.sv");
  auto status = analyzer.Analyze();
  
  // May fail to parse, but should not crash
  // Just verify we can attempt the parse
  EXPECT_NO_FATAL_FAILURE({
    analyzer.Analyze();
  }) << "Unbalanced markers should not cause crashes";
}

}  // namespace
}  // namespace verilog

