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

// Week 8: Code Block Arguments Tests
// Tests for macros that take code blocks (begin/end, fork/join) as arguments

#include <string>

#include "gtest/gtest.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Helper function to parse SystemVerilog code
bool ParsesSuccessfully(const char* code) {
  VerilogAnalyzer analyzer(code, "test.sv");
  const auto status = analyzer.Analyze();
  return status.ok() && analyzer.SyntaxTree() != nullptr;
}

// Week 8 Test 1: Begin/end block as macro argument
TEST(CodeBlockArgs, BeginEndBlock) {
  const char* code = R"(
`define EXECUTE_BLOCK(body) \
  begin \
    body \
  end

module test;
  initial begin
    `EXECUTE_BLOCK(
      begin
        $display("Statement 1");
        $display("Statement 2");
      end
    )
  end
endmodule
)";
  
  // Challenge: begin/end block passed as macro argument
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Begin/end block should work as macro argument";
}

// Week 8 Test 2: Multiple statements as code block
TEST(CodeBlockArgs, MultipleStatements) {
  const char* code = R"(
`define LOOP_BODY(stmts) \
  for (int i = 0; i < 10; i++) begin \
    stmts \
  end

module test;
  initial begin
    `LOOP_BODY(
      $display("Iteration %0d", i);
      data[i] = i * 2;
    )
  end
endmodule
)";
  
  // Multiple statements (without explicit begin/end)
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Multiple statements should work as macro argument";
}

// Week 8 Test 3: Fork/join block as argument
TEST(CodeBlockArgs, ForkJoinBlock) {
  const char* code = R"(
`define PARALLEL_BLOCK(body) \
  fork \
    body \
  join_none

module test;
  initial begin
    `PARALLEL_BLOCK(
      fork
        #10 $display("Thread 1");
        #20 $display("Thread 2");
      join
    )
  end
endmodule
)";
  
  // Fork/join block as argument
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Fork/join block should work as macro argument";
}

// Week 8 Test 4: Nested control structures
TEST(CodeBlockArgs, NestedControl) {
  const char* code = R"(
`define WITH_CONTROL(body) \
  if (enable) begin \
    body \
  end

module test;
  logic enable;
  initial begin
    `WITH_CONTROL(
      for (int i = 0; i < 5; i++) begin
        if (i % 2 == 0)
          $display("Even: %0d", i);
      end
    )
  end
endmodule
)";
  
  // Nested control structures (if, for) as argument
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Nested control structures should work";
}

// Week 8 Test 5: Case statement as argument
TEST(CodeBlockArgs, CaseStatement) {
  const char* code = R"(
`define HANDLE_CASE(cases) \
  case (state) \
    cases \
  endcase

module test;
  typedef enum {IDLE, RUN, DONE} state_t;
  state_t state;
  
  initial begin
    `HANDLE_CASE(
      IDLE: $display("Idle");
      RUN: $display("Running");
      DONE: $display("Done");
    )
  end
endmodule
)";
  
  // Case items as argument
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Case statement items should work as argument";
}

// Week 8 Test 6: Always block as argument
TEST(CodeBlockArgs, AlwaysBlock) {
  const char* code = R"(
`define GEN_ALWAYS(body) \
  always @(posedge clk) begin \
    body \
  end

module test(input clk);
  logic [7:0] data;
  
  `GEN_ALWAYS(
    data <= data + 1;
    if (data == 255)
      data <= 0;
  )
endmodule
)";
  
  // Sequential statements in always block
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Always block body should work as argument";
}

// Week 8 Test 7: Function call with code block
TEST(CodeBlockArgs, FunctionBody) {
  const char* code = R"(
`define GEN_FUNCTION(name, body) \
  function void name(); \
    body \
  endfunction

module test;
  `GEN_FUNCTION(print_hello,
    $display("Hello");
    $display("World");
  )
  
  initial print_hello();
endmodule
)";
  
  // Function body as argument
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Function body should work as macro argument";
}

// Week 8 Test 8: UVM-style sequence body macro
TEST(CodeBlockArgs, UVMSequenceBody) {
  const char* code = R"(
`define uvm_do_with(item, constraints) \
  begin \
    item = new(); \
    assert(item.randomize() with constraints); \
    send(item); \
  end

class my_sequence extends uvm_sequence#(my_item);
  task body();
    my_item item;
    `uvm_do_with(item, {
      addr inside {[0:100]};
      data < 256;
    })
  endtask
endclass
)";
  
  // UVM pattern: constraint block as argument
  // This combines code block with constraint syntax
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "UVM sequence with constraint block should parse";
}

// Week 8 Test 9: OpenTitan-style loop macro
TEST(CodeBlockArgs, OpenTitanLoopMacro) {
  const char* code = R"(
`define loop_ral_models(body) \
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

class cip_base_vseq;
  virtual task dut_init();
    `loop_ral_models(
      $display("Init model: %s", ral_name);
    )
  endtask
endclass
)";
  
  // Real OpenTitan pattern: complex nested fork/join with automatic variables
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "OpenTitan loop macro pattern should parse";
}

// Week 8 Test 10: Code block with declarations
TEST(CodeBlockArgs, BlockWithDeclarations) {
  const char* code = R"(
`define SCOPED_BLOCK(body) \
  begin : scoped \
    body \
  end

module test;
  initial begin
    `SCOPED_BLOCK(
      logic [7:0] temp;
      temp = 42;
      $display("Temp = %0d", temp);
    )
  end
endmodule
)";
  
  // Code block with local variable declarations
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Code block with declarations should work";
}

}  // namespace
}  // namespace verilog

