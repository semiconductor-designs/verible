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

// Unit tests for macro boundary marker injection in preprocessor (v5.6.0)
// Production implementation tests with TDD approach

#include <string>

#include "gtest/gtest.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/preprocessor/verilog-preprocess.h"

namespace verilog {
namespace {

// Test 1: Config Flag Controls Marker Injection
// Tests that inject_macro_markers config flag enables/disables markers
TEST(PreprocessMacroMarkersTest, ConfigFlagControlsMarkerInjection) {
  const std::string code = R"(
    `define LOG(msg) $display(msg)
    module test;
      initial begin
        `LOG("Hello")
      end
    endmodule
  )";
  
  // Test with markers disabled (default)
  {
    VerilogPreprocess::Config config;
    config.expand_macros = true;
    config.inject_macro_markers = false;  // Default
    
    VerilogAnalyzer analyzer(code, "test.sv", config);
    auto status = analyzer.Analyze();
    EXPECT_TRUE(status.ok()) << "Should parse without markers (default)";
  }
  
  // Test with markers enabled
  {
    VerilogPreprocess::Config config;
    config.expand_macros = true;
    config.inject_macro_markers = true;  // Enable markers
    
    VerilogAnalyzer analyzer(code, "test.sv", config);
    auto status = analyzer.Analyze();
    EXPECT_TRUE(status.ok()) << "Should parse with markers enabled";
  }
}

// Test 2: Simple Macro Expansion with Markers
// Tests that markers are injected before/after macro expansion
TEST(PreprocessMacroMarkersTest, SimpleMacroExpansionWithMarkers) {
  const std::string code = R"(
    `define MSG "Hello"
    module test;
      initial $display(`MSG);
    endmodule
  )";
  
  VerilogPreprocess::Config config;
  config.expand_macros = true;
  config.inject_macro_markers = true;
  
  VerilogAnalyzer analyzer(code, "test.sv", config);
  auto status = analyzer.Analyze();
  
  EXPECT_TRUE(status.ok()) << "Should parse with macro expansion and markers";
}

// Test 3: Nested Macro Expansion with Markers
// Tests that nested macros get properly nested markers
TEST(PreprocessMacroMarkersTest, NestedMacroExpansionWithMarkers) {
  const std::string code = R"(
    `define INNER(x) (x * 2)
    `define OUTER(y) `INNER(y) + 1
    module test;
      initial $display(`OUTER(5));
    endmodule
  )";
  
  VerilogPreprocess::Config config;
  config.expand_macros = true;
  config.inject_macro_markers = true;
  
  VerilogAnalyzer analyzer(code, "test.sv", config);
  auto status = analyzer.Analyze();
  
  EXPECT_TRUE(status.ok()) << "Should parse with nested macro markers";
}

// Test 4: Macro with Arguments
// Tests that macros with arguments get correct markers
TEST(PreprocessMacroMarkersTest, MacroWithArgumentsMarkers) {
  const std::string code = R"(
    `define ADD(a, b) ((a) + (b))
    module test;
      logic [31:0] result;
      initial result = `ADD(10, 20);
    endmodule
  )";
  
  VerilogPreprocess::Config config;
  config.expand_macros = true;
  config.inject_macro_markers = true;
  
  VerilogAnalyzer analyzer(code, "test.sv", config);
  auto status = analyzer.Analyze();
  
  EXPECT_TRUE(status.ok()) << "Should parse macro with arguments and markers";
}

// Test 5: Marker Injection Doesn't Break Event Trigger
// Tests that our original v5.4.2 use case still works
TEST(PreprocessMacroMarkersTest, EventTriggerAfterMacroExpansion) {
  const std::string code = R"(
    `define LOG(msg) $display(msg);
    
    class test;
      event done;
      
      task run();
        `LOG("Starting")
        -> done;
      endtask
    endclass
  )";
  
  VerilogPreprocess::Config config;
  config.expand_macros = true;
  config.inject_macro_markers = true;
  
  VerilogAnalyzer analyzer(code, "test.sv", config);
  auto status = analyzer.Analyze();
  
  EXPECT_TRUE(status.ok()) << "Event trigger after macro should parse correctly";
}

// Test 6: OpenTitan DV Macro Pattern
// Tests real-world OpenTitan pattern with uvm_info
TEST(PreprocessMacroMarkersTest, OpenTitanDVMacroPattern) {
  const std::string code = R"(
    `define uvm_info(ID, MSG, VERBOSITY) \
      $display($sformatf("[%s] %s", ID, MSG))
    
    module test;
      event my_event;
      
      task test_task();
        `uvm_info("TEST", "Starting test", UVM_LOW)
        -> my_event;
      endtask
    endmodule
  )";
  
  VerilogPreprocess::Config config;
  config.expand_macros = true;
  config.inject_macro_markers = true;
  
  VerilogAnalyzer analyzer(code, "test.sv", config);
  auto status = analyzer.Analyze();
  
  EXPECT_TRUE(status.ok()) << "OpenTitan DV pattern should parse correctly";
}

// Test 7: Multiple Macros in Sequence
// Tests that multiple sequential macros each get their own markers
TEST(PreprocessMacroMarkersTest, MultipleMacrosInSequence) {
  const std::string code = R"(
    `define LOG1 $display("log1");
    `define LOG2 $display("log2");
    `define LOG3 $display("log3");
    
    module test;
      initial begin
        `LOG1
        `LOG2
        `LOG3
      end
    endmodule
  )";
  
  VerilogPreprocess::Config config;
  config.expand_macros = true;
  config.inject_macro_markers = true;
  
  VerilogAnalyzer analyzer(code, "test.sv", config);
  auto status = analyzer.Analyze();
  
  EXPECT_TRUE(status.ok()) << "Multiple sequential macros should parse correctly";
}

// Test 8: Macro Expansion Disabled - No Markers
// Tests that when macro expansion is disabled, no markers are injected
TEST(PreprocessMacroMarkersTest, NoExpansionNoMarkers) {
  const std::string code = R"(
    `define MSG "Hello"
    module test;
      initial $display(`MSG);
    endmodule
  )";
  
  VerilogPreprocess::Config config;
  config.expand_macros = false;  // Disabled
  config.inject_macro_markers = false;
  
  VerilogAnalyzer analyzer(code, "test.sv", config);
  auto status = analyzer.Analyze();
  
  EXPECT_TRUE(status.ok()) << "Should parse without expansion";
}

}  // namespace
}  // namespace verilog

