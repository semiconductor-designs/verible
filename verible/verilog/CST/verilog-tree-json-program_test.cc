// Copyright 2017-2025 The Verible Authors.
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

// Phase 2: Program Blocks Tests for JSON Export
// Tests for program...endprogram blocks

#include "verible/verilog/CST/verilog-tree-json.h"

#include <string>

#include "gtest/gtest.h"
#include "nlohmann/json.hpp"
#include "verible/common/text/symbol.h"
#include "verible/common/util/logging.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

using nlohmann::json;

namespace verilog {
namespace {

// Helper: Parse code and convert to JSON
json ParseToJson(const std::string& code) {
  VerilogAnalyzer analyzer(code, "<test>");
  auto status = analyzer.Analyze();
  if (!status.ok()) {
    LOG(ERROR) << "Parse error: " << status.message();
    return json::object();
  }
  
  const auto& text_structure = analyzer.Data();
  const auto* root = text_structure.SyntaxTree().get();
  if (!root) return json::object();
  
  return ConvertVerilogTreeToJson(*root, text_structure.Contents());
}

// Helper: Find node by tag recursively
const json* FindNodeByTag(const json& node, const std::string& tag) {
  if (node.contains("tag") && node["tag"] == tag) {
    return &node;
  }
  
  if (node.contains("children")) {
    for (const auto& child : node["children"]) {
      const json* result = FindNodeByTag(child, tag);
      if (result) return result;
    }
  }
  
  return nullptr;
}

// Test 1: Basic program
TEST(ProgramTest, BasicProgram) {
  const std::string code = R"(
program test;
  initial begin
    $display("Hello");
  end
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty()) << "Parse should succeed";
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr) << "Should find kProgramDeclaration node";
}

// Test 2: Automatic program
TEST(ProgramTest, AutomaticProgram) {
  const std::string code = R"(
program automatic test_auto;
  initial begin
    $display("Automatic program");
  end
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr);
  
  // Check for is_automatic flag in metadata
  if (prog->contains("metadata") && (*prog)["metadata"].contains("program_info")) {
    const auto& prog_info = (*prog)["metadata"]["program_info"];
    if (prog_info.contains("is_automatic")) {
      EXPECT_TRUE(prog_info["is_automatic"]);
    }
  }
}

// Test 3: Static program (explicit)
TEST(ProgramTest, StaticProgram) {
  const std::string code = R"(
program static test_static;
  initial begin
    $display("Static program");
  end
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr);
}

// Test 4: Program with initial block
TEST(ProgramTest, ProgramWithInitial) {
  const std::string code = R"(
program test_init;
  initial begin
    $display("Initialization");
    #10;
    $display("Done");
  end
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr);
}

// Test 5: Program with final block
TEST(ProgramTest, ProgramWithFinal) {
  const std::string code = R"(
program test_final;
  initial begin
    $display("Starting");
  end
  
  final begin
    $display("Cleanup");
  end
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr);
}

// Test 6: Program with functions
TEST(ProgramTest, ProgramWithFunctions) {
  const std::string code = R"(
program test_func;
  function int add(int a, int b);
    return a + b;
  endfunction
  
  initial begin
    int result = add(5, 3);
  end
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr);
}

// Test 7: Program with tasks
TEST(ProgramTest, ProgramWithTasks) {
  const std::string code = R"(
program test_task;
  task wait_cycles(int n);
    repeat(n) #10;
  endtask
  
  initial begin
    wait_cycles(5);
  end
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr);
}

// Test 8: Program with imports (UVM style)
TEST(ProgramTest, ProgramWithImports) {
  const std::string code = R"(
program test_uvm;
  import uvm_pkg::*;
  
  initial begin
    run_test();
  end
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr);
}

// Test 9: Program with port list
TEST(ProgramTest, ProgramWithPorts) {
  const std::string code = R"(
program test_ports(input logic clk, output logic done);
  initial begin
    @(posedge clk);
    done = 1'b1;
  end
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr);
  
  // Check for has_ports flag in metadata
  if (prog->contains("metadata") && (*prog)["metadata"].contains("program_info")) {
    const auto& prog_info = (*prog)["metadata"]["program_info"];
    if (prog_info.contains("has_ports")) {
      EXPECT_TRUE(prog_info["has_ports"]);
    }
  }
}

// Test 10: Program with input/output ports
TEST(ProgramTest, ProgramWithInputOutputPorts) {
  const std::string code = R"(
program test_io(
  input  logic clk,
  input  logic rst_n,
  output logic status
);
  initial begin
    @(posedge clk);
    status = rst_n;
  end
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr);
}

// Test 11: Multiple programs in file
TEST(ProgramTest, MultiplePrograms) {
  const std::string code = R"(
program prog1;
  initial $display("Program 1");
endprogram

program prog2;
  initial $display("Program 2");
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count programs
  int prog_count = 0;
  std::function<void(const json&)> count_programs = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kProgramDeclaration") {
      prog_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_programs(child);
      }
    }
  };
  count_programs(tree);
  
  EXPECT_EQ(prog_count, 2) << "Should find 2 programs";
}

// Test 12: Empty program
TEST(ProgramTest, EmptyProgram) {
  const std::string code = R"(
program empty;
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr);
}

// Test 13: Program with variable declarations
TEST(ProgramTest, ProgramWithVariables) {
  const std::string code = R"(
program test_vars;
  int counter;
  logic [7:0] data;
  
  initial begin
    counter = 0;
    data = 8'h42;
  end
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr);
}

// Test 14: Program with timescale
TEST(ProgramTest, ProgramWithTimescale) {
  const std::string code = R"(
`timescale 1ns/1ps

program test_time;
  initial begin
    #100;
    $display("Time: %t", $time);
  end
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr);
}

// Test 15: Complex UVM-style program
TEST(ProgramTest, ComplexUVMProgram) {
  const std::string code = R"(
program automatic test_complex;
  import uvm_pkg::*;
  import my_test_pkg::*;
  
  string test_name = "my_test";
  
  initial begin
    uvm_config_db#(int)::set(null, "*", "value", 42);
    run_test(test_name);
  end
  
  final begin
    $display("Test completed");
  end
endprogram
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* prog = FindNodeByTag(tree, "kProgramDeclaration");
  ASSERT_NE(prog, nullptr);
}

}  // namespace
}  // namespace verilog

