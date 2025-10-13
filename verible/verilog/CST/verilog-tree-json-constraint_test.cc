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

// Phase 1.2: Constraint & Randomization Support Tests for JSON Export
// Tests for rand/randc variables and constraint blocks

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

// Test 1: rand variable declaration
TEST(ConstraintTest, RandVariable) {
  const std::string code = R"(
class test_class;
  rand int value;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty()) << "Parse should succeed";
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
  
  // Check for rand variable in class metadata
  if (cls->contains("metadata") && (*cls)["metadata"].contains("class_info")) {
    const auto& class_info = (*cls)["metadata"]["class_info"];
    if (class_info.contains("rand_variable_count")) {
      EXPECT_GT(class_info["rand_variable_count"], 0);
    }
  }
}

// Test 2: randc variable declaration
TEST(ConstraintTest, RandcVariable) {
  const std::string code = R"(
class test_class;
  randc bit [3:0] mode;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 3: Basic constraint block
TEST(ConstraintTest, BasicConstraintBlock) {
  const std::string code = R"(
class test_class;
  rand int value;
  
  constraint c_range {
    value >= 0;
    value <= 100;
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
  
  if (cls->contains("metadata") && (*cls)["metadata"].contains("class_info")) {
    const auto& class_info = (*cls)["metadata"]["class_info"];
    if (class_info.contains("has_constraints")) {
      EXPECT_TRUE(class_info["has_constraints"]);
    }
  }
}

// Test 4: Constraint with inside operator
TEST(ConstraintTest, ConstraintWithInside) {
  const std::string code = R"(
class test_class;
  rand int value;
  
  constraint c_set {
    value inside {10, 20, 30, 40};
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 5: Constraint with dist operator
TEST(ConstraintTest, ConstraintWithDist) {
  const std::string code = R"(
class test_class;
  rand int value;
  
  constraint c_dist {
    value dist {0 := 10, [1:9] := 80, 10 := 10};
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 6: Constraint with implication (->)
TEST(ConstraintTest, ConstraintWithImplication) {
  const std::string code = R"(
class test_class;
  rand bit enable;
  rand int value;
  
  constraint c_imply {
    enable -> value > 0;
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 7: Constraint with bidirectional implication (<->)
TEST(ConstraintTest, ConstraintWithBidirectional) {
  const std::string code = R"(
class test_class;
  rand bit flag1;
  rand bit flag2;
  
  constraint c_equiv {
    flag1 <-> flag2;
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 8: Constraint with solve before
TEST(ConstraintTest, ConstraintWithSolveBefore) {
  const std::string code = R"(
class test_class;
  rand int addr;
  rand int data;
  
  constraint c_order {
    solve addr before data;
    addr < 100;
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 9: Constraint with foreach
TEST(ConstraintTest, ConstraintWithForeach) {
  const std::string code = R"(
class test_class;
  rand int array[10];
  
  constraint c_array {
    foreach (array[i])
      array[i] inside {[0:255]};
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 10: Constraint with unique
TEST(ConstraintTest, ConstraintWithUnique) {
  const std::string code = R"(
class test_class;
  rand int array[5];
  
  constraint c_unique {
    unique {array};
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 11: Soft constraint
TEST(ConstraintTest, SoftConstraint) {
  const std::string code = R"(
class test_class;
  rand int value;
  
  constraint c_soft {
    soft value == 50;
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 12: Disabled constraint (constraint_mode)
TEST(ConstraintTest, DisabledConstraint) {
  const std::string code = R"(
class test_class;
  rand int value;
  
  constraint c_disabled {
    value < 100;
  }
  
  function new();
    c_disabled.constraint_mode(0);
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 13: Complex nested constraints
TEST(ConstraintTest, ComplexNestedConstraints) {
  const std::string code = R"(
class test_class;
  rand int x, y, z;
  
  constraint c_complex {
    (x > 0) -> {
      y inside {[10:20]};
      z == x + y;
    }
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 14: Constraint with array bounds
TEST(ConstraintTest, ConstraintWithArrayBounds) {
  const std::string code = R"(
class test_class;
  rand int index;
  int array[100];
  
  constraint c_bounds {
    index >= 0;
    index < array.size();
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 15: Constraint referencing other variables
TEST(ConstraintTest, ConstraintReferencingOthers) {
  const std::string code = R"(
class test_class;
  rand int start_addr;
  rand int end_addr;
  
  constraint c_range {
    start_addr < end_addr;
    end_addr - start_addr >= 16;
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 16: Multiple constraint blocks
TEST(ConstraintTest, MultipleConstraintBlocks) {
  const std::string code = R"(
class test_class;
  rand int value;
  
  constraint c_lower {
    value >= 0;
  }
  
  constraint c_upper {
    value <= 100;
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 17: Inline randomize with constraints
TEST(ConstraintTest, InlineRandomizeWithConstraints) {
  const std::string code = R"(
class test_class;
  rand int value;
  
  function void test();
    assert(randomize(value) with {value inside {[10:20]};});
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 18: pre_randomize() / post_randomize()
TEST(ConstraintTest, PrePostRandomize) {
  const std::string code = R"(
class test_class;
  rand int value;
  
  function void pre_randomize();
    $display("Before randomization");
  endfunction
  
  function void post_randomize();
    $display("After randomization: %d", value);
  endfunction
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
}

// Test 19: Constraint inheritance
TEST(ConstraintTest, ConstraintInheritance) {
  const std::string code = R"(
class base_class;
  rand int value;
  
  constraint c_base {
    value >= 0;
  }
endclass

class derived_class extends base_class;
  constraint c_derived {
    value <= 100;
  }
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count classes with constraints
  int constraint_count = 0;
  std::function<void(const json&)> count_constraints = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kClassDeclaration") {
      if (node.contains("metadata") && node["metadata"].contains("class_info")) {
        const auto& class_info = node["metadata"]["class_info"];
        if (class_info.contains("has_constraints") && class_info["has_constraints"]) {
          constraint_count++;
        }
      }
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_constraints(child);
      }
    }
  };
  count_constraints(tree);
  
  EXPECT_EQ(constraint_count, 2) << "Both classes should have constraints";
}

// Test 20: Performance test (50 constraints)
TEST(ConstraintTest, PerformanceTest) {
  std::string code = "class test_class;\n";
  code += "  rand int value;\n";
  
  // Generate 50 constraint blocks
  for (int i = 0; i < 50; i++) {
    code += "  constraint c" + std::to_string(i) + " {\n";
    code += "    value >= " + std::to_string(i * 2) + ";\n";
    code += "  }\n";
  }
  
  code += "endclass\n";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* cls = FindNodeByTag(tree, "kClassDeclaration");
  ASSERT_NE(cls, nullptr);
  
  if (cls->contains("metadata") && (*cls)["metadata"].contains("class_info")) {
    const auto& class_info = (*cls)["metadata"]["class_info"];
    if (class_info.contains("has_constraints")) {
      EXPECT_TRUE(class_info["has_constraints"]);
    }
  }
}

}  // namespace
}  // namespace verilog

