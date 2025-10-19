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

// Week 7: Complex Argument Parsing Tests
// Tests for handling complex macro arguments with nested structures

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

// Week 7 Test 1: Comma inside type parameters
// Challenge: `MyClass#(int, string)` - comma is NOT an argument separator
TEST(ComplexArgs, CommaInTypeParameter) {
  const char* code = R"(
class my_item extends uvm_sequence_item;
  `uvm_object_param_utils_begin(my_item#(int, string))
  `uvm_object_utils_end
endclass
)";
  
  // Week 7 Day 1-2: This test will initially FAIL
  // Need to track that comma is inside #(...) not between macro args
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Comma inside type parameter should not split arguments";
}

// Week 7 Test 2: Multiple nested type parameters
TEST(ComplexArgs, NestedTypeParameters) {
  const char* code = R"(
class complex_vseq #(
  type RAL_T = uvm_reg_block,
  type CFG_T = my_cfg#(int, bit)
) extends uvm_sequence;
  `uvm_object_param_utils_begin(complex_vseq#(RAL_T, CFG_T))
  `uvm_object_utils_end
endclass
)";
  
  // Nested type parameters: CFG_T = my_cfg#(int, bit)
  // Then used in macro: complex_vseq#(RAL_T, CFG_T)
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Nested type parameters should parse correctly";
}

// Week 7 Test 3: Braces in constraint block argument
TEST(ComplexArgs, BracesInConstraint) {
  const char* code = R"(
class my_sequence extends uvm_sequence#(my_item);
  task body();
    my_item item;
    `uvm_do_with(item, {addr inside {[0:100]}; data < 256;})
  endtask
endclass
)";
  
  // Challenge: Nested braces {addr inside {[0:100]}; ...}
  // Outer {...} is constraint block (one macro argument)
  // Inner {...} is set notation for 'inside'
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Nested braces in constraint should be treated as one argument";
}

// Week 7 Test 4: Mixed nesting - parens, brackets, braces
TEST(ComplexArgs, MixedNesting) {
  const char* code = R"(
class test_seq extends uvm_sequence#(test_item);
  task body();
    test_item item;
    `uvm_do_with(item, {
      addr inside {[0:100], [200:300]};
      data dist {[0:10] := 5, [11:20] :/ 3};
      size inside {4, 8, 16};
    })
  endtask
endclass
)";
  
  // Complex nesting:
  // {...} outer constraint block
  //   {[0:100], [200:300]} set with ranges
  //   {[0:10] := 5, ...} distribution weights
  //   {4, 8, 16} value set
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Mixed nesting of parens/brackets/braces should work";
}

// Week 7 Test 5: Comma in function call within macro
TEST(ComplexArgs, CommaInFunctionCall) {
  const char* code = R"(
class my_test extends uvm_test;
  task run_phase(uvm_phase phase);
    `uvm_info("TEST", $sformatf("Value: %0d, Status: %s", value, status), UVM_LOW)
  endtask
endclass
)";
  
  // $sformatf has commas: $sformatf("...", value, status)
  // But uvm_info macro has 3 args: (ID, MSG, VERBOSITY)
  // MSG contains the $sformatf with commas
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Commas in function calls should not split macro arguments";
}

// Week 7 Test 6: Triple nested type parameters
TEST(ComplexArgs, TripleNestedTypeParams) {
  const char* code = R"(
class deep_vseq #(
  type T1 = container#(item#(int, bit), string)
) extends uvm_sequence;
  `uvm_object_param_utils_begin(deep_vseq#(T1))
  `uvm_object_utils_end
endclass
)";
  
  // T1 = container#(item#(int, bit), string)
  // Three levels of nesting
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Triple nested type parameters should parse";
}

// Week 7 Test 7: Parentheses in expression argument
TEST(ComplexArgs, ParensInExpression) {
  const char* code = R"(
class calc_seq extends uvm_sequence#(my_item);
  task body();
    my_item item;
    `uvm_do_with(item, {data == ((addr + offset) * multiplier);})
  endtask
endclass
)";
  
  // Expression with nested parentheses: ((addr + offset) * multiplier)
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Parentheses in expressions should not confuse argument parsing";
}

// Week 7 Test 8: Begin/end block as argument
TEST(ComplexArgs, BeginEndBlock) {
  const char* code = R"(
class fork_seq extends uvm_sequence#(my_item);
  task body();
    fork
      begin
        // Hypothetical macro taking begin/end block
        my_item item;
        `uvm_do(item)
      end
    join_none
  endtask
endclass
)";
  
  // This is simpler - begin/end inside fork/join
  // Week 8 will handle begin/end AS macro argument
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Begin/end blocks should parse correctly";
}

// Week 7 Test 9: Array indexing with expressions
TEST(ComplexArgs, ArrayIndexing) {
  const char* code = R"(
class array_seq extends uvm_sequence#(my_item);
  task body();
    my_item items[10];
    `uvm_do_with(items[i], {data == arr[i+1][j];})
  endtask
endclass
)";
  
  // Array indexing: items[i], arr[i+1][j]
  // Brackets contain expressions with operators
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Array indexing should not confuse bracket counting";
}

// Week 7 Test 10: All delimiters combined
TEST(ComplexArgs, AllDelimitersCombined) {
  const char* code = R"(
class ultimate_seq extends uvm_sequence#(item#(int, bit));
  task body();
    item#(int, bit) obj;
    `uvm_do_with(obj, {
      addr inside {[0:100], [200:arr[idx]]};
      data dist {(val1 + val2) := weight, [min:max] :/ 10};
      size == ((base << shift) & mask);
    })
  endtask
endclass
)";
  
  // Ultimate complexity test:
  // - Type parameters: item#(int, bit)
  // - Nested braces: constraint block, set notation, distribution
  // - Nested brackets: ranges, array indexing
  // - Nested parens: expressions, operators
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "All delimiters combined should parse correctly";
}

}  // namespace
}  // namespace verilog

