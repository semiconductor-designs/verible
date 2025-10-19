// Copyright 2025
// Verible UVM Enhancement - Type Parameter Tests
// Week 17: Phase 4.1 - Type Parameter Support

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

// Test 1: Simple type parameter with default
TEST(TypeParams, SimpleTypeParameter) {
  const char* code = R"(
class my_class #(type T = int);
  T data;
  
  function new();
    data = 0;
  endfunction
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Simple type parameter with default should parse";
}

// Test 2: Multiple type parameters
TEST(TypeParams, MultipleTypeParameters) {
  const char* code = R"(
class my_class #(type T1 = int, type T2 = bit);
  T1 data1;
  T2 data2;
  
  function new();
    data1 = 0;
    data2 = 0;
  endfunction
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Multiple type parameters should parse";
}

// Test 3: Type parameter without default
TEST(TypeParams, TypeParameterNoDefault) {
  const char* code = R"(
class my_class #(type T);
  T data;
  
  function new(T init_val);
    data = init_val;
  endfunction
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Type parameter without default should parse";
}

// Test 4: Type parameter in extends clause
TEST(TypeParams, TypeParameterInExtends) {
  const char* code = R"(
class base_class #(type T = int);
  T base_data;
endclass

class derived_class #(type T = int) extends base_class #(T);
  T derived_data;
  
  function new();
    base_data = 0;
    derived_data = 0;
  endfunction
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Type parameter in extends clause should parse";
}

// Test 5: Type parameter with complex default type
TEST(TypeParams, ComplexDefaultType) {
  const char* code = R"(
class my_class #(type T = logic [7:0]);
  T data;
  
  function new();
    data = 8'h00;
  endfunction
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Type parameter with complex default type should parse";
}

// Test 6: Type parameter used in array declaration
TEST(TypeParams, TypeParameterInArray) {
  const char* code = R"(
class my_class #(type T = int);
  T data_array[10];
  T queue_data[$];
  
  function new();
    foreach (data_array[i]) begin
      data_array[i] = 0;
    end
  endfunction
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Type parameter used in array declarations should parse";
}

// Test 7: Type parameter in function return type
TEST(TypeParams, TypeParameterInFunctionReturn) {
  const char* code = R"(
class my_class #(type T = int);
  T data;
  
  function T get_data();
    return data;
  endfunction
  
  function void set_data(T value);
    data = value;
  endfunction
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Type parameter in function return type and arguments should parse";
}

// Test 8: Mixed type and value parameters
TEST(TypeParams, MixedTypeAndValueParameters) {
  const char* code = R"(
class my_class #(
  type T = int,
  int WIDTH = 32
);
  T data;
  logic [WIDTH-1:0] bus;
  
  function new();
    data = 0;
    bus = '0;
  endfunction
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Mixed type and value parameters should parse";
}

// Test 9: Type parameter in constraint
TEST(TypeParams, TypeParameterInConstraint) {
  const char* code = R"(
class my_class #(type T = int);
  rand T data;
  
  constraint data_c {
    data inside {[0:100]};
  }
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Type parameter used in constraint should parse";
}

// Test 10: Nested class with type parameter
TEST(TypeParams, NestedTypeParameter) {
  const char* code = R"(
class outer_class #(type T = int);
  T outer_data;
  
  class inner_class;
    T inner_data;
    
    function new(T init_val);
      inner_data = init_val;
    endfunction
  endclass
  
  inner_class inner_inst;
  
  function new();
    outer_data = 0;
    inner_inst = new(outer_data);
  endfunction
endclass
)";
  
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Nested class using outer type parameter should parse";
}

}  // namespace
}  // namespace verilog
