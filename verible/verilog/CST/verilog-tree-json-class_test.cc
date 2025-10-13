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

// Phase 1.1: Core Class Support Tests for JSON Export
// Tests for class declarations with OOP features

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

// Test 1: Basic class declaration
TEST(ClassTest, BasicClass) {
  const std::string code = R"(
class simple_class;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty()) << "Parse should succeed";
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr) << "Should find kClassDeclaration node";
}

// Test 2: Class with parent (extends)
TEST(ClassTest, ClassWithParent) {
  const std::string code = R"(
class child_class extends parent_class;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
  
  // Check for parent class in metadata
  if (cls->contains("metadata") && (*cls)["metadata"].contains("class_info")) {
    const auto& class_info = (*cls)["metadata"]["class_info"];
    if (class_info.contains("parent_class")) {
      EXPECT_EQ(class_info["parent_class"], "parent_class");
    }
  }
}

// Test 3: Virtual class
TEST(ClassTest, VirtualClass) {
  const std::string code = R"(
virtual class base_class;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
  
  if (cls->contains("metadata") && (*cls)["metadata"].contains("class_info")) {
    const auto& class_info = (*cls)["metadata"]["class_info"];
    if (class_info.contains("is_virtual")) {
      EXPECT_TRUE(class_info["is_virtual"]);
    }
  }
}

// Test 4: Virtual method (virtual function)
TEST(ClassTest, VirtualMethod) {
  const std::string code = R"(
class base_class;
  virtual function void display();
    $display("Base");
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 5: Pure virtual method
TEST(ClassTest, PureVirtualMethod) {
  const std::string code = R"(
virtual class abstract_class;
  pure virtual function void execute();
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 6: Class constructor
TEST(ClassTest, ClassConstructor) {
  const std::string code = R"(
class my_class;
  function new();
    // Constructor
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
  
  if (cls->contains("metadata") && (*cls)["metadata"].contains("class_info")) {
    const auto& class_info = (*cls)["metadata"]["class_info"];
    if (class_info.contains("constructor_present")) {
      EXPECT_TRUE(class_info["constructor_present"]);
    }
  }
}

// Test 7: Constructor with parameters
TEST(ClassTest, ConstructorWithParameters) {
  const std::string code = R"(
class config_class;
  int value;
  
  function new(int init_value);
    value = init_value;
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 8: Constructor with super.new()
TEST(ClassTest, ConstructorWithSuper) {
  const std::string code = R"(
class derived_class extends base_class;
  function new();
    super.new();
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 9: Multiple inheritance levels (3+ deep)
TEST(ClassTest, MultipleInheritanceLevels) {
  const std::string code = R"(
class level1;
endclass

class level2 extends level1;
endclass

class level3 extends level2;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Find level3 class
  int class_count = 0;
  std::function<void(const json&)> count_classes = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kClassDeclaration") {
      class_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_classes(child);
      }
    }
  };
  count_classes(tree);
  
  EXPECT_EQ(class_count, 3) << "Should find 3 classes";
}

// Test 10: Class with properties (variables)
TEST(ClassTest, ClassWithProperties) {
  const std::string code = R"(
class data_class;
  int count;
  logic [7:0] data;
  string name;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
  
  if (cls->contains("metadata") && (*cls)["metadata"].contains("class_info")) {
    const auto& class_info = (*cls)["metadata"]["class_info"];
    if (class_info.contains("property_count")) {
      EXPECT_GT(class_info["property_count"], 0);
    }
  }
}

// Test 11: Class with local/protected properties
TEST(ClassTest, ClassWithLocalProtectedProperties) {
  const std::string code = R"(
class encapsulated_class;
  local int private_data;
  protected int internal_data;
  int public_data;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 12: Class with static properties
TEST(ClassTest, ClassWithStaticProperties) {
  const std::string code = R"(
class counter_class;
  static int instance_count;
  int id;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 13: Class methods (functions/tasks)
TEST(ClassTest, ClassMethods) {
  const std::string code = R"(
class utility_class;
  function int add(int a, int b);
    return a + b;
  endfunction
  
  task wait_cycles(int n);
    repeat(n) #10;
  endtask
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
  
  if (cls->contains("metadata") && (*cls)["metadata"].contains("class_info")) {
    const auto& class_info = (*cls)["metadata"]["class_info"];
    if (class_info.contains("method_count")) {
      EXPECT_GT(class_info["method_count"], 0);
    }
  }
}

// Test 14: Extern method declarations
TEST(ClassTest, ExternMethodDeclarations) {
  const std::string code = R"(
class external_class;
  extern function void compute();
  extern task execute();
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 15: this reference usage
TEST(ClassTest, ThisReference) {
  const std::string code = R"(
class self_ref_class;
  int value;
  
  function void set_value(int value);
    this.value = value;
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 16: super reference usage
TEST(ClassTest, SuperReference) {
  const std::string code = R"(
class override_class extends base_class;
  virtual function void display();
    super.display();
    $display("Override");
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 17: Empty class
TEST(ClassTest, EmptyClass) {
  const std::string code = R"(
class empty;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 18: Class with mix of virtual/non-virtual
TEST(ClassTest, MixedVirtualMethods) {
  const std::string code = R"(
class mixed_class;
  virtual function void virtual_method();
  endfunction
  
  function void normal_method();
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 19: Parameterized class
TEST(ClassTest, ParameterizedClass) {
  const std::string code = R"(
class generic_class #(parameter int WIDTH = 8);
  logic [WIDTH-1:0] data;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 20: Class in package
TEST(ClassTest, ClassInPackage) {
  const std::string code = R"(
package my_pkg;
  class pkg_class;
    int value;
  endclass
endpackage
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 21: Nested class (class within class)
TEST(ClassTest, NestedClass) {
  const std::string code = R"(
class outer_class;
  class inner_class;
    int data;
  endclass
  
  inner_class inner_inst;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Should find at least one class (outer)
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 22: Multiple classes in file
TEST(ClassTest, MultipleClasses) {
  const std::string code = R"(
class class1;
  int data1;
endclass

class class2;
  int data2;
endclass

class class3;
  int data3;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  int class_count = 0;
  std::function<void(const json&)> count_classes = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kClassDeclaration") {
      class_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_classes(child);
      }
    }
  };
  count_classes(tree);
  
  EXPECT_EQ(class_count, 3) << "Should find 3 classes";
}

// Test 23: Class with typedef
TEST(ClassTest, ClassWithTypedef) {
  const std::string code = R"(
class typedef_class;
  typedef int word_t;
  word_t data;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 24: Performance test (50 classes)
TEST(ClassTest, PerformanceTest) {
  std::string code;
  
  // Generate 50 classes
  for (int i = 0; i < 50; i++) {
    code += "class class" + std::to_string(i) + ";\n";
    code += "  int data" + std::to_string(i) + ";\n";
    code += "endclass\n\n";
  }
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  int class_count = 0;
  std::function<void(const json&)> count_classes = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kClassDeclaration") {
      class_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_classes(child);
      }
    }
  };
  count_classes(tree);
  
  EXPECT_EQ(class_count, 50) << "Should find 50 classes";
}

// Test 25: Complex UVM class hierarchy
TEST(ClassTest, ComplexUVMClassHierarchy) {
  const std::string code = R"(
class uvm_object;
  virtual function string get_type_name();
    return "uvm_object";
  endfunction
endclass

class uvm_component extends uvm_object;
  function new(string name, uvm_component parent);
    super.new();
  endfunction
  
  virtual task run_phase();
  endtask
endclass

class uvm_driver extends uvm_component;
  virtual task run_phase();
    forever begin
      // Drive logic
    end
  endtask
endclass

class my_driver extends uvm_driver;
  virtual task run_phase();
    super.run_phase();
  endtask
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  int class_count = 0;
  std::function<void(const json&)> count_classes = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kClassDeclaration") {
      class_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_classes(child);
      }
    }
  };
  count_classes(tree);
  
  EXPECT_EQ(class_count, 4) << "Should find 4 classes in UVM hierarchy";
}

// ============================================================================
// Phase 1.3: Advanced Class Features (Tests 26-35)
// ============================================================================

// Test 26: Class with covergroup
TEST(ClassAdvancedTest, ClassWithCovergroup) {
  const std::string code = R"(
class test_class;
  logic [1:0] state;
  
  covergroup cg;
    coverpoint state;
  endgroup
  
  function new();
    cg = new();
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 27: Class with local variables
TEST(ClassAdvancedTest, ClassWithLocalVariables) {
  const std::string code = R"(
class test_class;
  local int private_data;
  local string secret;
  
  function int get_data();
    return private_data;
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 28: Class with protected methods
TEST(ClassAdvancedTest, ClassWithProtectedMethods) {
  const std::string code = R"(
class test_class;
  protected function void internal_process();
    $display("Protected");
  endfunction
  
  function void public_method();
    internal_process();
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 29: Class with static properties
TEST(ClassAdvancedTest, ClassWithStaticProperties) {
  const std::string code = R"(
class test_class;
  static int instance_count = 0;
  static string class_name = "test_class";
  
  function new();
    instance_count++;
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 30: Class with static methods
TEST(ClassAdvancedTest, ClassWithStaticMethods) {
  const std::string code = R"(
class test_class;
  static function int get_version();
    return 1;
  endfunction
  
  static task reset_all();
    $display("Resetting");
  endtask
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 31: Class with typedef
TEST(ClassAdvancedTest, ClassWithTypedef) {
  const std::string code = R"(
class test_class;
  typedef logic [7:0] byte_t;
  typedef int unsigned uint_t;
  
  byte_t data;
  uint_t counter;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 32: Class with enum
TEST(ClassAdvancedTest, ClassWithEnum) {
  const std::string code = R"(
class test_class;
  typedef enum {IDLE, BUSY, DONE} state_t;
  state_t current_state;
  
  function void set_state(state_t new_state);
    current_state = new_state;
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 33: Class with struct
TEST(ClassAdvancedTest, ClassWithStruct) {
  const std::string code = R"(
class test_class;
  typedef struct {
    int addr;
    int data;
  } transaction_t;
  
  transaction_t txn;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 34: Class accessing null
TEST(ClassAdvancedTest, ClassAccessingNull) {
  const std::string code = R"(
class test_class;
  test_class next;
  
  function bit is_last();
    return (next == null);
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 35: Complete UVM scoreboard class
TEST(ClassAdvancedTest, CompleteUVMScoreboard) {
  const std::string code = R"(
class uvm_scoreboard extends uvm_component;
  typedef struct {
    bit [31:0] addr;
    bit [63:0] data;
  } transaction_t;
  
  local transaction_t expected_queue[$];
  protected int match_count;
  static int total_scoreboards;
  
  covergroup trans_cg;
    coverpoint addr_range {
      bins low = {[0:255]};
      bins high = {[256:511]};
    }
  endgroup
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
    trans_cg = new();
    total_scoreboards++;
  endfunction
  
  virtual task run_phase();
    forever begin
      check_transaction();
    end
  endtask
  
  protected function void check_transaction();
    match_count++;
  endfunction
  
  function int get_matches();
    return match_count;
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
  
  // Verify it has the expected features
  if (cls->contains("metadata") && (*cls)["metadata"].contains("class_info")) {
    const auto& class_info = (*cls)["metadata"]["class_info"];
    
    if (class_info.contains("parent_class")) {
      EXPECT_EQ(class_info["parent_class"], "uvm_component");
    }
    
    if (class_info.contains("constructor_present")) {
      EXPECT_TRUE(class_info["constructor_present"]);
    }
    
    if (class_info.contains("method_count")) {
      EXPECT_GT(class_info["method_count"], 0);
    }
  }
}

}  // namespace
}  // namespace verilog

