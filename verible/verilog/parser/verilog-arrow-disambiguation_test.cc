// Copyright 2017-2024 The Verible Authors.
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

// v5.6.0 Week 9-10: Comprehensive test suite for arrow disambiguation
// Tests both macro-aware and enhanced heuristic modes

#include <memory>
#include <string>

#include "gtest/gtest.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/preprocessor/verilog-preprocess.h"

namespace verilog {
namespace {

// Helper function to parse and check for success
bool ParseSucceeds(const std::string& code, 
                   LexicalContext::DisambiguationMode mode = 
                       LexicalContext::DisambiguationMode::kMacroAware) {
  VerilogAnalyzer analyzer(code, "test.sv");
  analyzer.SetArrowDisambiguationMode(mode);
  const auto status = analyzer.Analyze();
  return status.ok();
}

// Test 1: Complex nested macros with event triggers
TEST(ArrowDisambiguationTest, ComplexNestedMacros) {
  const std::string code = R"(
`define LOG(msg) $display(msg)
`define TRIGGER_EVENT(e) -> e

module test;
  event evt;
  task automatic my_task();
    `LOG("Before event")
    `TRIGGER_EVENT(evt)
    `LOG("After event")
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 2: Macro-in-macro expansion
TEST(ArrowDisambiguationTest, MacroInMacroExpansion) {
  const std::string code = R"(
`define INNER(x) -> x
`define OUTER(y) begin `INNER(y) end

module test;
  event e;
  task test_task();
    `OUTER(e);
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
}

// Test 3: Deep nesting stress test (10 levels)
TEST(ArrowDisambiguationTest, DeepNestingStress) {
  const std::string code = R"(
`define L1(x) `L2(x)
`define L2(x) `L3(x)
`define L3(x) `L4(x)
`define L4(x) `L5(x)
`define L5(x) `L6(x)
`define L6(x) `L7(x)
`define L7(x) `L8(x)
`define L8(x) `L9(x)
`define L9(x) `L10(x)
`define L10(x) -> x

module test;
  event e;
  task deep();
    `L1(e);
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
}

// Test 4: Event trigger after function call
TEST(ArrowDisambiguationTest, EventTriggerAfterFunctionCall) {
  const std::string code = R"(
module test;
  event e;
  function void my_func(); endfunction
  
  task test_task();
    my_func();
    -> e;
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 5: Event trigger after array access
TEST(ArrowDisambiguationTest, EventTriggerAfterArrayAccess) {
  const std::string code = R"(
module test;
  event e;
  int array[10];
  
  task test_task();
    array[0] = 42;
    -> e;
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 6: Logical implication in expression
TEST(ArrowDisambiguationTest, LogicalImplicationInExpression) {
  const std::string code = R"(
module test;
  logic a, b, result;
  
  always_comb begin
    result = a -> b;
  end
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 7: Mixed event triggers and implications
TEST(ArrowDisambiguationTest, MixedTriggersAndImplications) {
  const std::string code = R"(
module test;
  event e;
  logic a, b, result;
  
  task test_task();
    result = a -> b;  // Implication
    -> e;             // Event trigger
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 8: Event trigger in initial block
TEST(ArrowDisambiguationTest, EventTriggerInInitial) {
  const std::string code = R"(
module test;
  event e;
  
  initial begin
    #10;
    -> e;
  end
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  // Note: Enhanced heuristic doesn't track initial/always context, only test macro-aware
}

// Test 9: Event trigger in always block
TEST(ArrowDisambiguationTest, EventTriggerInAlways) {
  const std::string code = R"(
module test;
  event e;
  logic clk;
  
  always @(posedge clk) begin
    -> e;
  end
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  // Note: Enhanced heuristic doesn't track initial/always context, only test macro-aware
}

// Test 10: Multiple event triggers in sequence
TEST(ArrowDisambiguationTest, MultipleEventTriggers) {
  const std::string code = R"(
module test;
  event e1, e2, e3;
  
  task test_task();
    -> e1;
    -> e2;
    -> e3;
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 11: Event trigger with delay
TEST(ArrowDisambiguationTest, EventTriggerWithDelay) {
  const std::string code = R"(
module test;
  event e;
  
  task test_task();
    #10 -> e;
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 12: Implication in assertion
TEST(ArrowDisambiguationTest, ImplicationInAssertion) {
  const std::string code = R"(
module test;
  logic clk, req, ack;
  
  property p;
    @(posedge clk) req -> ack;
  endproperty
  
  assert property (p);
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 13: Conditional event trigger
TEST(ArrowDisambiguationTest, ConditionalEventTrigger) {
  const std::string code = R"(
module test;
  event e;
  logic cond;
  
  task test_task();
    if (cond)
      -> e;
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 14: Event trigger in fork-join
TEST(ArrowDisambiguationTest, EventTriggerInForkJoin) {
  const std::string code = R"(
module test;
  event e1, e2;
  
  task test_task();
    fork
      -> e1;
      -> e2;
    join
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 15: Implication in constraint block
TEST(ArrowDisambiguationTest, ImplicationInConstraint) {
  const std::string code = R"(
class test_class;
  rand bit a, b;
  
  constraint c {
    a -> b;
  }
endclass
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 16: Event trigger after macro call (OpenTitan pattern)
TEST(ArrowDisambiguationTest, EventTriggerAfterMacroCall) {
  const std::string code = R"(
`define uvm_info(ID, MSG, VERBOSITY) $display($sformatf("[%s] %s", ID, MSG))

module test;
  event e;
  
  task test_task();
    `uvm_info("TEST", "Message", 100)
    -> e;
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
}

// Test 17: Nested tasks with event triggers
// Note: SystemVerilog doesn't allow nested task declarations, so we test nested calls instead
TEST(ArrowDisambiguationTest, NestedTasksWithEventTriggers) {
  const std::string code = R"(
module test;
  event e;
  
  task inner_task();
    -> e;
  endtask
  
  task outer_task();
    inner_task();
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 18: Event trigger in class method
TEST(ArrowDisambiguationTest, EventTriggerInClassMethod) {
  const std::string code = R"(
class test_class;
  event e;
  
  task my_method();
    -> e;
  endtask
endclass
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 19: Complex expression with implication
TEST(ArrowDisambiguationTest, ComplexExpressionWithImplication) {
  const std::string code = R"(
module test;
  logic a, b, c, d, result;
  
  always_comb begin
    result = (a && b) -> (c || d);
  end
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 20: Event trigger with hierarchical reference
TEST(ArrowDisambiguationTest, EventTriggerWithHierarchicalRef) {
  const std::string code = R"(
module sub;
  event e;
endmodule

module test;
  sub u_sub();
  
  task test_task();
    -> u_sub.e;
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kEnhancedHeuristic));
}

// Test 21: Performance stress test with many macros
TEST(ArrowDisambiguationTest, PerformanceStressManyMacros) {
  std::string code = R"(
`define TRIGGER(e) -> e
module test;
  event e;
  task stress_test();
)";
  
  // Generate 100 event triggers
  for (int i = 0; i < 100; ++i) {
    code += "    `TRIGGER(e);\n";
  }
  
  code += R"(
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kMacroAware));
}

// Test 22: A/B comparison mode (should not crash)
TEST(ArrowDisambiguationTest, ABTestingModeDoesNotCrash) {
  const std::string code = R"(
module test;
  event e;
  task test_task();
    -> e;
  endtask
endmodule
)";
  
  EXPECT_TRUE(ParseSucceeds(code, LexicalContext::DisambiguationMode::kBoth));
}

}  // namespace
}  // namespace verilog

