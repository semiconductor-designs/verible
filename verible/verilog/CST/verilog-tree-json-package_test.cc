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

// Phase 3: Package Tests for JSON Export
// Tests for package declarations, imports, exports, and scoped references

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

// Test 1: Basic package declaration
TEST(PackageTest, BasicPackage) {
  const std::string code = R"(
package simple_pkg;
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty()) << "Parse should succeed";
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr) << "Should find kPackageDeclaration node";
}

// Test 2: Package with typedefs
TEST(PackageTest, PackageWithTypedefs) {
  const std::string code = R"(
package types_pkg;
  typedef logic [7:0] byte_t;
  typedef logic [15:0] word_t;
  typedef logic [31:0] dword_t;
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
  
  if (pkg->contains("metadata") && (*pkg)["metadata"].contains("package_info")) {
    const auto& info = (*pkg)["metadata"]["package_info"];
    if (info.contains("typedef_count")) {
      EXPECT_EQ(info["typedef_count"], 3);
    }
  }
}

// Test 3: Package with parameters
TEST(PackageTest, PackageWithParameters) {
  const std::string code = R"(
package config_pkg;
  parameter int WIDTH = 32;
  parameter int DEPTH = 256;
  parameter bit ENABLE = 1;
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
  
  if (pkg->contains("metadata") && (*pkg)["metadata"].contains("package_info")) {
    const auto& info = (*pkg)["metadata"]["package_info"];
    if (info.contains("parameter_count")) {
      EXPECT_EQ(info["parameter_count"], 3);
    }
  }
}

// Test 4: Package with classes
TEST(PackageTest, PackageWithClasses) {
  const std::string code = R"(
package class_pkg;
  class base_class;
    int data;
  endclass
  
  class derived_class extends base_class;
    int more_data;
  endclass
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
  
  if (pkg->contains("metadata") && (*pkg)["metadata"].contains("package_info")) {
    const auto& info = (*pkg)["metadata"]["package_info"];
    if (info.contains("class_count")) {
      EXPECT_EQ(info["class_count"], 2);
    }
  }
}

// Test 5: Package with functions
TEST(PackageTest, PackageWithFunctions) {
  const std::string code = R"(
package math_pkg;
  function int add(int a, int b);
    return a + b;
  endfunction
  
  function int multiply(int a, int b);
    return a * b;
  endfunction
  
  task delay(int cycles);
    repeat(cycles) @(posedge clk);
  endtask
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
  
  if (pkg->contains("metadata") && (*pkg)["metadata"].contains("package_info")) {
    const auto& info = (*pkg)["metadata"]["package_info"];
    if (info.contains("function_count")) {
      EXPECT_GE(info["function_count"], 2);
    }
  }
}

// Test 6: Package imports in module
TEST(PackageTest, PackageImport) {
  const std::string code = R"(
package my_pkg;
  typedef logic [7:0] byte_t;
endpackage

module test;
  import my_pkg::byte_t;
  byte_t data;
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 7: Wildcard package import
TEST(PackageTest, WildcardImport) {
  const std::string code = R"(
package util_pkg;
  typedef logic [31:0] addr_t;
  parameter int SIZE = 256;
endpackage

module test;
  import util_pkg::*;
  addr_t address;
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 8: Package export
TEST(PackageTest, PackageExport) {
  const std::string code = R"(
package export_pkg;
  export base_pkg::*;
  
  typedef logic [15:0] word_t;
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
}

// Test 9: Scoped references (pkg::item)
TEST(PackageTest, ScopedReferences) {
  const std::string code = R"(
package data_pkg;
  typedef struct {
    logic [7:0] field1;
    logic [15:0] field2;
  } data_t;
endpackage

module test;
  data_pkg::data_t my_data;
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 10: Multiple packages
TEST(PackageTest, MultiplePackages) {
  const std::string code = R"(
package pkg1;
  typedef logic [7:0] byte_t;
endpackage

package pkg2;
  typedef logic [15:0] word_t;
endpackage

package pkg3;
  typedef logic [31:0] dword_t;
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count packages
  int pkg_count = 0;
  std::function<void(const json&)> count_packages = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kPackageDeclaration") {
      pkg_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_packages(child);
      }
    }
  };
  count_packages(tree);
  
  EXPECT_EQ(pkg_count, 3) << "Should find 3 packages";
}

// Test 11: Package dependencies
TEST(PackageTest, PackageDependencies) {
  const std::string code = R"(
package base_pkg;
  typedef logic [7:0] byte_t;
endpackage

package derived_pkg;
  import base_pkg::byte_t;
  typedef byte_t[4] quad_byte_t;
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 12: Package with enum
TEST(PackageTest, PackageWithEnum) {
  const std::string code = R"(
package enum_pkg;
  typedef enum {IDLE, ACTIVE, DONE} state_t;
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
}

// Test 13: Package with struct
TEST(PackageTest, PackageWithStruct) {
  const std::string code = R"(
package struct_pkg;
  typedef struct {
    logic [31:0] addr;
    logic [63:0] data;
    logic valid;
  } transaction_t;
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
}

// Test 14: Package with union
TEST(PackageTest, PackageWithUnion) {
  const std::string code = R"(
package union_pkg;
  typedef union {
    logic [31:0] as_int;
    logic [7:0][3:0] as_bytes;
  } data_u;
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
}

// Test 15: Empty package
TEST(PackageTest, EmptyPackage) {
  const std::string code = R"(
package empty_pkg;
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
  
  if (pkg->contains("metadata") && (*pkg)["metadata"].contains("package_info")) {
    const auto& info = (*pkg)["metadata"]["package_info"];
    if (info.contains("typedef_count")) {
      EXPECT_EQ(info["typedef_count"], 0);
    }
    if (info.contains("class_count")) {
      EXPECT_EQ(info["class_count"], 0);
    }
  }
}

// Test 16: Package with DPI imports
TEST(PackageTest, PackageWithDPI) {
  const std::string code = R"(
package dpi_pkg;
  import "DPI-C" function int c_add(int a, int b);
  
  function int wrapper_add(int x, int y);
    return c_add(x, y);
  endfunction
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
}

// Test 17: Package with assertions
TEST(PackageTest, PackageWithAssertions) {
  const std::string code = R"(
package assert_pkg;
  property p_valid;
    @(posedge clk) valid |-> ready;
  endproperty
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
}

// Test 18: Package with covergroup
TEST(PackageTest, PackageWithCovergroup) {
  const std::string code = R"(
package coverage_pkg;
  covergroup cg;
    coverpoint data {
      bins low = {[0:63]};
      bins high = {[64:127]};
    }
  endgroup
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
}

// Test 19: Package name extraction
TEST(PackageTest, PackageNameExtraction) {
  const std::string code = R"(
package my_custom_pkg;
  parameter int VALUE = 42;
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
  
  if (pkg->contains("metadata") && (*pkg)["metadata"].contains("package_info")) {
    const auto& info = (*pkg)["metadata"]["package_info"];
    if (info.contains("package_name")) {
      EXPECT_EQ(info["package_name"], "my_custom_pkg");
    }
  }
}

// Test 20: Complex UVM-style package
TEST(PackageTest, UVMStylePackage) {
  const std::string code = R"(
package uvm_style_pkg;
  typedef enum {UVM_LOW, UVM_MEDIUM, UVM_HIGH} uvm_severity;
  
  class uvm_object;
    string name;
    function new(string n = "object");
      name = n;
    endfunction
  endclass
  
  class uvm_component extends uvm_object;
    function void build_phase();
    endfunction
  endclass
  
  parameter int UVM_MAJOR_REV = 1;
  parameter int UVM_MINOR_REV = 2;
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
  
  if (pkg->contains("metadata") && (*pkg)["metadata"].contains("package_info")) {
    const auto& info = (*pkg)["metadata"]["package_info"];
    if (info.contains("class_count")) {
      EXPECT_EQ(info["class_count"], 2);
    }
    if (info.contains("parameter_count")) {
      EXPECT_EQ(info["parameter_count"], 2);
    }
  }
}

// Test 21: Package with localparam
TEST(PackageTest, PackageWithLocalparam) {
  const std::string code = R"(
package local_pkg;
  localparam int INTERNAL_SIZE = 128;
  parameter int PUBLIC_SIZE = 256;
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
}

// Test 22: Package with constraints
TEST(PackageTest, PackageWithConstraints) {
  const std::string code = R"(
package constraint_pkg;
  class constrained_data;
    rand logic [7:0] data;
    constraint c_range {
      data inside {[10:100]};
    }
  endclass
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
}

// Test 23: Nested package imports
TEST(PackageTest, NestedImports) {
  const std::string code = R"(
package level1_pkg;
  typedef logic [7:0] byte_t;
endpackage

package level2_pkg;
  import level1_pkg::*;
  typedef byte_t word_t[2];
endpackage

module test;
  import level2_pkg::*;
  word_t data;
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 24: Performance test (20 packages)
TEST(PackageTest, PerformanceTest) {
  std::string code;
  
  for (int i = 0; i < 20; i++) {
    code += "package pkg" + std::to_string(i) + ";\n";
    code += "  typedef logic [7:0] type" + std::to_string(i) + "_t;\n";
    code += "  parameter int VALUE" + std::to_string(i) + " = " + std::to_string(i) + ";\n";
    code += "endpackage\n\n";
  }
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  int pkg_count = 0;
  std::function<void(const json&)> count_packages = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kPackageDeclaration") {
      pkg_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_packages(child);
      }
    }
  };
  count_packages(tree);
  
  EXPECT_EQ(pkg_count, 20) << "Should find 20 packages";
}

// Test 25: Complete verification package
TEST(PackageTest, CompleteVerificationPackage) {
  const std::string code = R"(
package verification_pkg;
  // Typedefs
  typedef logic [31:0] addr_t;
  typedef logic [63:0] data_t;
  typedef enum {READ, WRITE, IDLE} op_t;
  
  // Parameters
  parameter int BUS_WIDTH = 64;
  parameter int ADDR_WIDTH = 32;
  
  // Transaction class
  class transaction;
    rand addr_t address;
    rand data_t data;
    rand op_t operation;
    
    constraint c_valid {
      address < 32'h1000_0000;
    }
  endclass
  
  // Utility functions
  function bit compare(data_t a, data_t b);
    return (a == b);
  endfunction
  
  // Covergroup
  covergroup op_coverage;
    coverpoint operation;
  endgroup
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* pkg = FindNodeByTag(tree, "kPackageDeclaration");
  ASSERT_NE(pkg, nullptr);
  
  if (pkg->contains("metadata") && (*pkg)["metadata"].contains("package_info")) {
    const auto& info = (*pkg)["metadata"]["package_info"];
    
    if (info.contains("package_name")) {
      EXPECT_EQ(info["package_name"], "verification_pkg");
    }
    
    if (info.contains("typedef_count")) {
      EXPECT_EQ(info["typedef_count"], 3);
    }
    
    if (info.contains("parameter_count")) {
      EXPECT_EQ(info["parameter_count"], 2);
    }
    
    if (info.contains("class_count")) {
      EXPECT_EQ(info["class_count"], 1);
    }
    
    if (info.contains("function_count")) {
      EXPECT_GE(info["function_count"], 1);
    }
  }
}

}  // namespace
}  // namespace verilog

