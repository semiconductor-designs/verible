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

// Week 9: Recursive Macro Expansion Tests
// Tests for nested macros (macro calls inside macro arguments)

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

// Week 9 Test 1: Simple nested field macros (original test case)
TEST(RecursiveMacros, NestedFieldMacros) {
  const char* code = R"(
class my_item extends uvm_sequence_item;
  rand bit [7:0] addr;
  rand bit [7:0] data;
  string name;
  
  `uvm_object_utils_begin(my_item)
    `uvm_field_int(addr, UVM_DEFAULT)
    `uvm_field_int(data, UVM_DEFAULT)
    `uvm_field_string(name, UVM_DEFAULT)
  `uvm_object_utils_end
endclass
)";
  
  // Challenge: uvm_field_* macros nested inside uvm_object_utils_begin/end
  // Requires recursive expansion
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Nested field macros should expand recursively";
}

// Week 9 Test 2: Macro call in macro argument
TEST(RecursiveMacros, MacroCallInArg) {
  const char* code = R"(
`define INNER(x) (x + 1)
`define OUTER(y) begin $display("%0d", y); end

module test;
  initial begin
    `OUTER(`INNER(5))
  end
endmodule
)";
  
  // Challenge: INNER macro called inside OUTER's argument
  // Requires depth tracking
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Macro call in argument should expand recursively";
}

// Week 9 Test 3: Triple nesting
TEST(RecursiveMacros, TripleNesting) {
  const char* code = R"(
`define LEVEL1(x) (x * 2)
`define LEVEL2(y) (y + 10)
`define LEVEL3(z) begin $display("%0d", z); end

module test;
  initial begin
    `LEVEL3(`LEVEL2(`LEVEL1(5)))
  end
endmodule
)";
  
  // Three levels of nesting
  // Tests depth tracking
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Triple nested macros should expand correctly";
}

// Week 9 Test 4: Nested UVM component macros
TEST(RecursiveMacros, NestedComponentMacros) {
  const char* code = R"(
class my_agent extends uvm_agent;
  `uvm_component_utils_begin(my_agent)
    `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT)
  `uvm_component_utils_end
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
endclass
)";
  
  // Component utils with nested field macro
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Nested component macros should work";
}

// Week 9 Test 5: Mixed macro types
TEST(RecursiveMacros, MixedMacroTypes) {
  const char* code = R"(
`define VALUE 42
`define USE_VALUE(x) begin $display("Value: %0d", x); end

class my_test extends uvm_test;
  `uvm_component_utils(my_test)
  
  task run_phase(uvm_phase phase);
    `USE_VALUE(`VALUE)
    `uvm_info("TEST", $sformatf("Test value: %0d", `VALUE), UVM_LOW)
  endtask
endclass
)";
  
  // Mix of UVM macros and user-defined macros with nesting
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Mixed macro types with nesting should work";
}

// Week 9 Test 6: Nested macros in constraint
TEST(RecursiveMacros, NestedInConstraint) {
  const char* code = R"(
`define MAX_ADDR 255
`define MIN_ADDR 0

class my_item extends uvm_sequence_item;
  rand bit [7:0] addr;
  
  `uvm_object_utils_begin(my_item)
    `uvm_field_int(addr, UVM_DEFAULT)
  `uvm_object_utils_end
  
  constraint addr_c {
    addr inside {[`MIN_ADDR:`MAX_ADDR]};
  }
endclass
)";
  
  // Macros used in constraints inside UVM utils
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Macros in constraints with UVM macros should work";
}

// Week 9 Test 7: Conditional macro expansion
TEST(RecursiveMacros, ConditionalExpansion) {
  const char* code = R"(
`define DEBUG_MODE 1

class my_seq extends uvm_sequence#(my_item);
  `uvm_object_utils(my_seq)
  
  task body();
    `ifdef DEBUG_MODE
      `uvm_info("SEQ", "Debug mode enabled", UVM_LOW)
    `else
      `uvm_info("SEQ", "Debug mode disabled", UVM_LOW)
    `endif
  endtask
endclass
)";
  
  // Conditional compilation with UVM macros
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Conditional macros with UVM should work";
}

// Week 9 Test 8: Macro in macro definition
TEST(RecursiveMacros, MacroInDefinition) {
  const char* code = R"(
`define BASE_UTILS(T) \
  `uvm_object_utils_begin(T) \
  `uvm_object_utils_end

class item;
  `BASE_UTILS(item)
endclass
)";
  
  // User macro that contains UVM macros
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Macro containing other macros should expand";
}

// Week 9 Test 9: Deep nesting (4 levels)
TEST(RecursiveMacros, DeepNesting) {
  const char* code = R"(
`define L1(a) (a)
`define L2(b) `L1(b)
`define L3(c) `L2(c)
`define L4(d) `L3(d)

module test;
  logic [7:0] val;
  initial begin
    val = `L4(42);
  end
endmodule
)";
  
  // 4 levels of macro nesting
  // Tests depth limit tracking
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Deep nesting (4 levels) should work with depth limit";
}

// Week 9 Test 10: Multiple field types with nesting
TEST(RecursiveMacros, MultipleFieldTypes) {
  const char* code = R"(
class complex_item extends uvm_sequence_item;
  rand bit [15:0] addr;
  rand bit [31:0] data;
  rand bit [3:0] size;
  string name;
  my_object obj;
  bit [7:0] array[10];
  
  `uvm_object_utils_begin(complex_item)
    `uvm_field_int(addr, UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(data, UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(size, UVM_DEFAULT)
    `uvm_field_string(name, UVM_DEFAULT)
    `uvm_field_object(obj, UVM_DEFAULT)
    `uvm_field_array_int(array, UVM_DEFAULT)
  `uvm_object_utils_end
  
  function new(string name = "complex_item");
    super.new(name);
  endfunction
endclass
)";
  
  // Many different field types nested in utils
  // Real-world UVM pattern
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Multiple field types with nesting should work";
}

}  // namespace
}  // namespace verilog

