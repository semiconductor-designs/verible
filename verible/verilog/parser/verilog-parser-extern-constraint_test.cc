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

// Week 11: Extern Constraint Tests
// Tests for SystemVerilog extern constraint declarations and out-of-body definitions
// This is a critical UVM feature for separating constraint declarations from their definitions

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

// Week 11 Test 1: Simple extern constraint declaration
TEST(ExternConstraint, Declaration) {
  const char* code = R"(
class test_item;
  rand int unsigned delay;
  extern constraint delay_c;
endclass
)";
  
  // TDD RED: extern keyword in constraint declaration
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Simple extern constraint declaration should parse";
}

// Week 11 Test 2: Out-of-body constraint definition
TEST(ExternConstraint, OutOfBodyDefinition) {
  const char* code = R"(
class test_item;
  rand int unsigned delay;
  extern constraint delay_c;
endclass

constraint test_item::delay_c {
  delay inside {[0:100]};
}
)";
  
  // TDD RED: Out-of-body constraint definition with scope resolution
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Out-of-body constraint definition should parse";
}

// Week 11 Test 3: Multiple extern constraints
TEST(ExternConstraint, MultipleExternConstraints) {
  const char* code = R"(
class transaction;
  bit [7:0] addr;
  bit [7:0] data;
  
  extern constraint addr_c;
  extern constraint data_c;
endclass

constraint transaction::addr_c {
  addr inside {[0:15]};
}

constraint transaction::data_c {
  data != 0;
}
)";
  
  // Multiple extern constraints with separate definitions
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Multiple extern constraints should parse";
}

// Week 11 Test 4: Extern constraint with soft keyword
TEST(ExternConstraint, SoftConstraint) {
  const char* code = R"(
class soft_item;
  int value;
  extern constraint value_c;
endclass

constraint soft_item::value_c {
  soft value inside {[10:20]};
}
)";
  
  // TDD RED: soft keyword in constraint expression
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Soft constraint should parse";
}

// Week 11 Test 5: Extern constraint with dist operator
TEST(ExternConstraint, DistConstraint) {
  const char* code = R"(
class weighted_item;
  int myval;
  
  constraint myval_c {
    myval dist {
      0 := 50,
      [1:5] := 30,
      [6:10] :/ 20
    };
  }
endclass
)";
  
  // TDD: dist operator with := and :/ weight syntaxes (inline constraint for now)
  // Note: Out-of-body dist constraints will be tested in Week 12-13
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Distribution constraint should parse";
}

// Week 11 Test 6: Extern constraint with implication
TEST(ExternConstraint, ImplicationConstraint) {
  const char* code = R"(
class conditional_item;
  rand bit enable;
  rand int unsigned value;
  extern constraint enable_value_c;
endclass

constraint conditional_item::enable_value_c {
  enable -> (value < 100);
  !enable -> (value == 0);
}
)";
  
  // TDD RED: Implication operator (->) in constraints
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Implication constraint should parse";
}

// Week 11 Test 7: Extern constraint with solve...before
TEST(ExternConstraint, SolveBeforeConstraint) {
  const char* code = R"(
class ordered_item;
  rand bit [7:0] addr;
  rand bit [7:0] data;
  extern constraint order_c;
endclass

constraint ordered_item::order_c {
  solve addr before data;
  data == addr * 2;
}
)";
  
  // TDD RED: solve...before ordering constraint
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "solve...before constraint should parse";
}

// Week 11 Test 8: Extern constraint in parameterized class
TEST(ExternConstraint, ParameterizedClassConstraint) {
  const char* code = R"(
class param_item #(int WIDTH = 8);
  rand bit [WIDTH-1:0] value;
  extern constraint value_c;
endclass

constraint param_item::value_c {
  value inside {[0:10]};
}
)";
  
  // Extern constraint in parameterized class
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Extern constraint in parameterized class should parse";
}

// Week 11 Test 9: Complex extern constraint with multiple operators
TEST(ExternConstraint, ComplexConstraint) {
  const char* code = R"(
class complex_item;
  rand bit [15:0] addr;
  rand bit [31:0] data;
  rand bit [3:0] size;
  rand bit write;
  
  extern constraint transaction_c;
endclass

constraint complex_item::transaction_c {
  soft addr inside {[0:4095]};
  
  size dist {
    0 := 10,
    1 := 20,
    [2:3] := 30,
    [4:15] :/ 40
  };
  
  write -> (data != 0);
  !write -> (size == 0);
  
  solve addr before size;
}
)";
  
  // Complex constraint combining soft, dist, implication, solve...before
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Complex extern constraint with multiple operators should parse";
}

// Week 11 Test 10: Extern constraint with inline and out-of-body mix
TEST(ExternConstraint, MixedConstraints) {
  const char* code = R"(
class mixed_item;
  rand bit [7:0] addr;
  rand bit [7:0] data;
  
  // Inline constraint
  constraint inline_c {
    addr < 128;
  }
  
  // Extern constraint
  extern constraint extern_c;
endclass

constraint mixed_item::extern_c {
  data inside {[0:255]};
  data != addr;
}
)";
  
  // Mix of inline and extern constraints in same class
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Mixed inline and extern constraints should parse";
}

}  // namespace
}  // namespace verilog
