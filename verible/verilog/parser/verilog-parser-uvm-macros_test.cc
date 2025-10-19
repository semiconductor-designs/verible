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

// Parser tests for UVM macro expansion
// Phase 2.3: Week 5 Day 1-2 - Test Specifications (TDD Red phase)
//
// These tests verify that the parser can handle UVM macros after
// they are expanded by the preprocessor.

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

// Test 1: Simple object utils macro
// Phase 2.3: Currently will FAIL - macro not expanded yet
TEST(UVMMacros, SimpleObjectUtils) {
  const char* code = R"(
class item;
  `uvm_object_utils(item)
endclass
)";
  
  // TDD RED: This will fail because uvm_object_utils is not expanded
  // Phase 2.3 Week 5 Day 3-5 will implement expansion
  // Expected after implementation: macro expands to factory registration code
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Simple uvm_object_utils should parse after macro expansion";
}

// Test 2: Object utils begin/end with field automation
// Phase 2.3: Currently will FAIL - nested macros not expanded
TEST(UVMMacros, ObjectUtilsBeginEnd) {
  const char* code = R"(
class item extends uvm_sequence_item;
  rand bit [7:0] data;
  
  `uvm_object_utils_begin(item)
    `uvm_field_int(data, UVM_DEFAULT)
  `uvm_object_utils_end
  
  function new(string name = "item");
    super.new(name);
  endfunction
endclass
)";
  
  // TDD RED: Nested macros (uvm_field_int inside uvm_object_utils_begin)
  // Phase 2.3 will implement nested expansion
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Object utils begin/end with field automation should parse";
}

// Test 3: Component utils macro
TEST(UVMMacros, ComponentUtils) {
  const char* code = R"(
class my_agent extends uvm_agent;
  `uvm_component_utils(my_agent)
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
endclass
)";
  
  // TDD RED: Component utils expansion not implemented
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Component utils should parse after expansion";
}

// Test 4: Reporting macros
TEST(UVMMacros, ReportingMacros) {
  const char* code = R"(
class my_test extends uvm_test;
  task run_phase(uvm_phase phase);
    `uvm_info("TEST", "Starting test", UVM_LOW)
    `uvm_warning("TEST", "This is a warning")
    `uvm_error("TEST", "This is an error")
  endtask
endclass
)";
  
  // TDD RED: Reporting macros not expanded
  // These should expand to function calls
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Reporting macros should parse after expansion";
}

// Test 5: Sequence macros
TEST(UVMMacros, SequenceMacros) {
  const char* code = R"(
class my_sequence extends uvm_sequence#(my_item);
  task body();
    my_item item;
    `uvm_do(item)
  endtask
endclass
)";
  
  // TDD RED: uvm_do not expanded
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Sequence macros should parse after expansion";
}

// Test 6: Field automation for different types
TEST(UVMMacros, FieldAutomationTypes) {
  const char* code = R"(
class my_config extends uvm_object;
  int unsigned addr;
  string name;
  my_object obj;
  
  `uvm_object_utils_begin(my_config)
    `uvm_field_int(addr, UVM_DEFAULT)
    `uvm_field_string(name, UVM_DEFAULT)
    `uvm_field_object(obj, UVM_DEFAULT)
  `uvm_object_utils_end
endclass
)";
  
  // TDD RED: Multiple field types not expanded
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Field automation for different types should parse";
}

// Test 7: Parameterized type utils
TEST(UVMMacros, ParameterizedTypeUtils) {
  const char* code = R"(
class base_vseq #(
  type RAL_T = uvm_reg_block,
  type CFG_T = base_cfg
) extends uvm_sequence;
  `uvm_object_param_utils_begin(base_vseq#(RAL_T, CFG_T))
  `uvm_object_utils_end
  
  RAL_T ral;
  CFG_T cfg;
endclass
)";
  
  // TDD RED: Parameterized type utils with type parameters not expanded
  // This is complex - involves stringification and type parameter handling
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Parameterized type utils should parse after expansion";
}

// Test 8: Analysis port declaration
TEST(UVMMacros, AnalysisPortDeclaration) {
  const char* code = R"(
class my_monitor extends uvm_monitor;
  `uvm_analysis_imp_decl(_received)
  
  uvm_analysis_imp_received#(my_item, my_monitor) item_port;
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
    item_port = new("item_port", this);
  endfunction
endclass
)";
  
  // TDD RED: Analysis imp declaration not expanded
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Analysis port declaration should parse after expansion";
}

// Test 9: Sequence do_with macro
TEST(UVMMacros, SequenceDoWith) {
  const char* code = R"(
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
  
  // TDD RED: uvm_do_with with inline constraints not expanded
  // This is complex - code block as macro argument
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Sequence do_with with constraints should parse";
}

// Test 10: Multiple macros in one class
TEST(UVMMacros, MultipleMacrosInClass) {
  const char* code = R"(
class complete_item extends uvm_sequence_item;
  rand bit [15:0] addr;
  rand bit [7:0] data;
  string name;
  
  `uvm_object_utils_begin(complete_item)
    `uvm_field_int(addr, UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(data, UVM_DEFAULT)
    `uvm_field_string(name, UVM_DEFAULT)
  `uvm_object_utils_end
  
  function new(string name = "complete_item");
    super.new(name);
  endfunction
  
  task do_something();
    `uvm_info("ITEM", $sformatf("addr=%0h data=%0h", addr, data), UVM_MEDIUM)
  endtask
endclass
)";
  
  // TDD RED: Multiple different macro types in one class
  // Tests interaction between object_utils, field_int, and reporting macros
  EXPECT_TRUE(ParsesSuccessfully(code))
      << "Multiple macros in one class should parse after expansion";
}

}  // namespace
}  // namespace verilog
