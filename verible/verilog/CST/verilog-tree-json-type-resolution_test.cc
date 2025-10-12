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

// Tests for Type Resolution Metadata in JSON export

#include <memory>
#include <string>

#include "gtest/gtest.h"
#include "nlohmann/json.hpp"
#include "verible/common/analysis/syntax-tree-search.h"
#include "verible/common/text/concrete-syntax-tree.h"
#include "verible/common/text/symbol.h"
#include "verible/common/text/text-structure.h"
#include "verible/common/util/logging.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/CST/verilog-tree-json.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

using nlohmann::json;

namespace verilog {
namespace {

// Helper: Parse SystemVerilog code and return JSON
json ParseModuleToJson(const std::string& code) {
  const auto analyzer = std::make_unique<VerilogAnalyzer>(code, "test.sv");
  const auto status = ABSL_DIE_IF_NULL(analyzer)->Analyze();
  EXPECT_TRUE(status.ok()) << status.message();
  
  const verible::SymbolPtr& tree = analyzer->SyntaxTree();
  if (!tree) return json();
  
  return ConvertVerilogTreeToJson(*tree, analyzer->Data().Contents());
}

// Helper: Find first node with specific tag and containing text
const json* FindNodeByTagAndText(const json& node, const std::string& tag,
                                  const std::string& text_contains) {
  if (node.contains("tag") && node["tag"] == tag) {
    if (node.contains("text")) {
      std::string text_str = node["text"].get<std::string>();
      if (text_str.find(text_contains) != std::string::npos) {
        return &node;
      }
    }
  }
  
  if (node.contains("children") && node["children"].is_array()) {
    for (const auto& child : node["children"]) {
      if (const json* found = FindNodeByTagAndText(child, tag, text_contains)) {
        return found;
      }
    }
  }
  
  return nullptr;
}

// ============================================================================
// TEST 1: Simple Typedef Resolution
// ============================================================================

TEST(TypeResolutionTest, SimpleTypedef) {
  const std::string code = R"(
module test;
  typedef logic [7:0] byte_t;
  byte_t data;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  // Find the variable declaration using byte_t
  const json* var_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "byte_t data");
  ASSERT_NE(var_decl, nullptr) << "Could not find variable declaration";
  
  // Check for type_info metadata
  ASSERT_TRUE(var_decl->contains("metadata")) << "No metadata found";
  const auto& metadata = (*var_decl)["metadata"];
  
  ASSERT_TRUE(metadata.contains("type_info")) << "No type_info in metadata";
  const auto& type_info = metadata["type_info"];
  
  // Verify type resolution
  EXPECT_EQ(type_info["declared_type"], "byte_t");
  EXPECT_EQ(type_info["resolved_type"], "logic [7:0]");
  EXPECT_TRUE(type_info["is_typedef"].get<bool>());
  EXPECT_EQ(type_info["base_type"], "logic");
  EXPECT_EQ(type_info["width"], 8);
  EXPECT_FALSE(type_info["signed"].get<bool>());
  EXPECT_TRUE(type_info["packed"].get<bool>());
}

// ============================================================================
// TEST 2: Nested Typedef Resolution
// ============================================================================

TEST(TypeResolutionTest, NestedTypedef) {
  const std::string code = R"(
module test;
  typedef logic [7:0] byte_t;
  typedef byte_t small_t;
  small_t data;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* var_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "small_t data");
  ASSERT_NE(var_decl, nullptr);
  
  ASSERT_TRUE(var_decl->contains("metadata"));
  const auto& type_info = (*var_decl)["metadata"]["type_info"];
  
  // Should resolve through the chain: small_t -> byte_t -> logic [7:0]
  EXPECT_EQ(type_info["declared_type"], "small_t");
  EXPECT_EQ(type_info["resolved_type"], "logic [7:0]");
  EXPECT_TRUE(type_info["is_typedef"].get<bool>());
  EXPECT_EQ(type_info["base_type"], "logic");
  EXPECT_EQ(type_info["width"], 8);
}

// ============================================================================
// TEST 3: Enum Type Resolution
// ============================================================================

TEST(TypeResolutionTest, EnumType) {
  const std::string code = R"(
module test;
  typedef enum logic [1:0] {
    IDLE = 0,
    ACTIVE = 1,
    DONE = 2
  } state_t;
  
  state_t current_state;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* var_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "state_t current_state");
  ASSERT_NE(var_decl, nullptr);
  
  ASSERT_TRUE(var_decl->contains("metadata"));
  const auto& type_info = (*var_decl)["metadata"]["type_info"];
  
  EXPECT_EQ(type_info["declared_type"], "state_t");
  EXPECT_EQ(type_info["resolved_type"], "enum logic [1:0]");
  EXPECT_TRUE(type_info["is_enum"].get<bool>());
  EXPECT_EQ(type_info["enum_member_count"], 3);
  EXPECT_EQ(type_info["base_type"], "logic");
  EXPECT_EQ(type_info["width"], 2);
}

// ============================================================================
// TEST 4: Struct Type Resolution
// ============================================================================

TEST(TypeResolutionTest, StructType) {
  const std::string code = R"(
module test;
  typedef struct packed {
    logic [7:0] addr;
    logic [31:0] data;
    logic valid;
  } bus_t;
  
  bus_t bus_signal;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* var_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "bus_t bus_signal");
  ASSERT_NE(var_decl, nullptr);
  
  ASSERT_TRUE(var_decl->contains("metadata"));
  const auto& type_info = (*var_decl)["metadata"]["type_info"];
  
  EXPECT_EQ(type_info["declared_type"], "bus_t");
  EXPECT_EQ(type_info["resolved_type"], "struct packed");
  EXPECT_TRUE(type_info["is_struct"].get<bool>());
  EXPECT_TRUE(type_info["packed"].get<bool>());
  EXPECT_EQ(type_info["struct_field_count"], 3);
  
  // Verify field names
  ASSERT_TRUE(type_info.contains("struct_fields"));
  const auto& fields = type_info["struct_fields"];
  ASSERT_TRUE(fields.is_array());
  EXPECT_EQ(fields.size(), 3);
  EXPECT_EQ(fields[0]["name"], "addr");
  EXPECT_EQ(fields[1]["name"], "data");
  EXPECT_EQ(fields[2]["name"], "valid");
}

// ============================================================================
// TEST 5: Union Type Resolution
// ============================================================================

TEST(TypeResolutionTest, UnionType) {
  const std::string code = R"(
module test;
  typedef union packed {
    logic [31:0] word;
    logic [7:0][3:0] bytes;
  } data_t;
  
  data_t data_union;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* var_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "data_t data_union");
  ASSERT_NE(var_decl, nullptr);
  
  ASSERT_TRUE(var_decl->contains("metadata"));
  const auto& type_info = (*var_decl)["metadata"]["type_info"];
  
  EXPECT_EQ(type_info["declared_type"], "data_t");
  EXPECT_EQ(type_info["resolved_type"], "union packed");
  EXPECT_TRUE(type_info["is_union"].get<bool>());
  EXPECT_TRUE(type_info["packed"].get<bool>());
  EXPECT_EQ(type_info["union_member_count"], 2);
}

// ============================================================================
// TEST 6: Parameterized Typedef
// ============================================================================

TEST(TypeResolutionTest, ParameterizedTypedef) {
  const std::string code = R"(
module test #(parameter WIDTH = 8);
  typedef logic [WIDTH-1:0] bus_t;
  bus_t data_bus;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* var_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "bus_t data_bus");
  ASSERT_NE(var_decl, nullptr);
  
  ASSERT_TRUE(var_decl->contains("metadata"));
  const auto& type_info = (*var_decl)["metadata"]["type_info"];
  
  EXPECT_EQ(type_info["declared_type"], "bus_t");
  EXPECT_EQ(type_info["resolved_type"], "logic [WIDTH-1:0]");
  EXPECT_TRUE(type_info["is_typedef"].get<bool>());
  EXPECT_TRUE(type_info["is_parameterized"].get<bool>());
  EXPECT_EQ(type_info["base_type"], "logic");
  // Width cannot be determined at parse time for parameterized types
  EXPECT_EQ(type_info["width"], -1);  // -1 indicates unknown/parameterized
}

// ============================================================================
// TEST 7: Signed/Unsigned Modifiers
// ============================================================================

TEST(TypeResolutionTest, SignedUnsignedModifiers) {
  const std::string code = R"(
module test;
  typedef logic signed [15:0] signed_t;
  typedef logic unsigned [15:0] unsigned_t;
  
  signed_t s_data;
  unsigned_t u_data;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  // Check signed type
  const json* s_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "signed_t s_data");
  ASSERT_NE(s_decl, nullptr);
  ASSERT_TRUE(s_decl->contains("metadata"));
  const auto& s_type_info = (*s_decl)["metadata"]["type_info"];
  
  EXPECT_EQ(s_type_info["declared_type"], "signed_t");
  EXPECT_TRUE(s_type_info["signed"].get<bool>());
  EXPECT_EQ(s_type_info["width"], 16);
  
  // Check unsigned type
  const json* u_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "unsigned_t u_data");
  ASSERT_NE(u_decl, nullptr);
  ASSERT_TRUE(u_decl->contains("metadata"));
  const auto& u_type_info = (*u_decl)["metadata"]["type_info"];
  
  EXPECT_EQ(u_type_info["declared_type"], "unsigned_t");
  EXPECT_FALSE(u_type_info["signed"].get<bool>());
  EXPECT_EQ(u_type_info["width"], 16);
}

// ============================================================================
// TEST 8: Packed/Unpacked Arrays
// ============================================================================

TEST(TypeResolutionTest, PackedUnpackedArrays) {
  const std::string code = R"(
module test;
  typedef logic [7:0][3:0] packed_array_t;
  typedef logic unpacked_array_t[16];
  
  packed_array_t p_arr;
  unpacked_array_t u_arr;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  // Check packed array
  const json* p_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "packed_array_t p_arr");
  ASSERT_NE(p_decl, nullptr);
  ASSERT_TRUE(p_decl->contains("metadata"));
  const auto& p_type_info = (*p_decl)["metadata"]["type_info"];
  
  EXPECT_EQ(p_type_info["declared_type"], "packed_array_t");
  EXPECT_TRUE(p_type_info["is_array"].get<bool>());
  EXPECT_TRUE(p_type_info["packed"].get<bool>());
  EXPECT_EQ(p_type_info["array_dimensions"], 2);
  
  // Check unpacked array
  const json* u_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "unpacked_array_t u_arr");
  ASSERT_NE(u_decl, nullptr);
  ASSERT_TRUE(u_decl->contains("metadata"));
  const auto& u_type_info = (*u_decl)["metadata"]["type_info"];
  
  EXPECT_EQ(u_type_info["declared_type"], "unpacked_array_t");
  EXPECT_TRUE(u_type_info["is_array"].get<bool>());
  EXPECT_FALSE(u_type_info["packed"].get<bool>());
  EXPECT_EQ(u_type_info["array_dimensions"], 1);
}

// ============================================================================
// TEST 9: Multidimensional Arrays
// ============================================================================

TEST(TypeResolutionTest, MultidimensionalArrays) {
  const std::string code = R"(
module test;
  typedef logic [7:0][3:0][1:0] multi_array_t;
  multi_array_t m_arr;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* var_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "multi_array_t m_arr");
  ASSERT_NE(var_decl, nullptr);
  
  ASSERT_TRUE(var_decl->contains("metadata"));
  const auto& type_info = (*var_decl)["metadata"]["type_info"];
  
  EXPECT_EQ(type_info["declared_type"], "multi_array_t");
  EXPECT_TRUE(type_info["is_array"].get<bool>());
  EXPECT_TRUE(type_info["packed"].get<bool>());
  EXPECT_EQ(type_info["array_dimensions"], 3);
  
  // Verify dimension sizes
  ASSERT_TRUE(type_info.contains("dimension_sizes"));
  const auto& dims = type_info["dimension_sizes"];
  ASSERT_TRUE(dims.is_array());
  EXPECT_EQ(dims.size(), 3);
  EXPECT_EQ(dims[0], 8);  // [7:0]
  EXPECT_EQ(dims[1], 4);  // [3:0]
  EXPECT_EQ(dims[2], 2);  // [1:0]
}

// ============================================================================
// TEST 10: Typedef with Enum Base
// ============================================================================

TEST(TypeResolutionTest, TypedefWithEnumBase) {
  const std::string code = R"(
module test;
  typedef enum logic [2:0] {
    RED, GREEN, BLUE
  } color_enum_t;
  
  typedef color_enum_t palette_t;
  palette_t my_color;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* var_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "palette_t my_color");
  ASSERT_NE(var_decl, nullptr);
  
  ASSERT_TRUE(var_decl->contains("metadata"));
  const auto& type_info = (*var_decl)["metadata"]["type_info"];
  
  EXPECT_EQ(type_info["declared_type"], "palette_t");
  EXPECT_EQ(type_info["resolved_type"], "enum logic [2:0]");
  EXPECT_TRUE(type_info["is_typedef"].get<bool>());
  EXPECT_TRUE(type_info["is_enum"].get<bool>());
  EXPECT_EQ(type_info["enum_member_count"], 3);
}

// ============================================================================
// TEST 11: Typedef with Struct Base
// ============================================================================

TEST(TypeResolutionTest, TypedefWithStructBase) {
  const std::string code = R"(
module test;
  typedef struct packed {
    logic [15:0] x;
    logic [15:0] y;
  } coord_t;
  
  typedef coord_t point_t;
  point_t location;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* var_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "point_t location");
  ASSERT_NE(var_decl, nullptr);
  
  ASSERT_TRUE(var_decl->contains("metadata"));
  const auto& type_info = (*var_decl)["metadata"]["type_info"];
  
  EXPECT_EQ(type_info["declared_type"], "point_t");
  EXPECT_EQ(type_info["resolved_type"], "struct packed");
  EXPECT_TRUE(type_info["is_typedef"].get<bool>());
  EXPECT_TRUE(type_info["is_struct"].get<bool>());
  EXPECT_EQ(type_info["struct_field_count"], 2);
}

// ============================================================================
// TEST 12: Forward Typedef References
// ============================================================================

TEST(TypeResolutionTest, ForwardTypedefReferences) {
  const std::string code = R"(
module test;
  // Use before definition (forward reference)
  forward_t data;
  
  typedef logic [31:0] forward_t;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* var_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "forward_t data");
  ASSERT_NE(var_decl, nullptr);
  
  ASSERT_TRUE(var_decl->contains("metadata"));
  const auto& type_info = (*var_decl)["metadata"]["type_info"];
  
  // Even with forward reference, should resolve if typedef is in same scope
  EXPECT_EQ(type_info["declared_type"], "forward_t");
  // Note: Forward resolution may require symbol table - for now, mark as unresolved
  EXPECT_TRUE(type_info.contains("is_forward_reference"));
  EXPECT_TRUE(type_info["is_forward_reference"].get<bool>());
}

// ============================================================================
// TEST 13: Package-Scoped Typedef
// ============================================================================

TEST(TypeResolutionTest, PackageScopedTypedef) {
  const std::string code = R"(
package my_pkg;
  typedef logic [63:0] word_t;
endpackage

module test;
  import my_pkg::*;
  my_pkg::word_t data;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* var_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "word_t data");
  ASSERT_NE(var_decl, nullptr);
  
  ASSERT_TRUE(var_decl->contains("metadata"));
  const auto& type_info = (*var_decl)["metadata"]["type_info"];
  
  EXPECT_EQ(type_info["declared_type"], "my_pkg::word_t");
  EXPECT_EQ(type_info["package_name"], "my_pkg");
  EXPECT_TRUE(type_info["is_package_scoped"].get<bool>());
  // Resolution across packages may require symbol table
  EXPECT_EQ(type_info["resolved_type"], "logic [63:0]");
}

// ============================================================================
// TEST 14: Negative Test - Unresolved Typedef
// ============================================================================

TEST(TypeResolutionTest, UnresolvedTypedef) {
  const std::string code = R"(
module test;
  // Reference to undefined type
  undefined_t data;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* var_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "undefined_t data");
  ASSERT_NE(var_decl, nullptr);
  
  ASSERT_TRUE(var_decl->contains("metadata"));
  const auto& type_info = (*var_decl)["metadata"]["type_info"];
  
  EXPECT_EQ(type_info["declared_type"], "undefined_t");
  EXPECT_TRUE(type_info.contains("is_unresolved"));
  EXPECT_TRUE(type_info["is_unresolved"].get<bool>());
  EXPECT_FALSE(type_info.contains("resolved_type"));
}

// ============================================================================
// TEST 15: Performance Test - 100 Nested Typedefs
// ============================================================================

TEST(TypeResolutionTest, Performance100NestedTypedefs) {
  // Build a chain of 100 typedefs
  std::string code = "module test;\n";
  code += "  typedef logic [7:0] type_0;\n";
  
  for (int i = 1; i < 100; ++i) {
    code += "  typedef type_" + std::to_string(i-1) + " type_" + std::to_string(i) + ";\n";
  }
  
  code += "  type_99 final_data;\n";
  code += "endmodule\n";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* var_decl = FindNodeByTagAndText(tree_json, "kDataDeclaration", "type_99 final_data");
  ASSERT_NE(var_decl, nullptr);
  
  ASSERT_TRUE(var_decl->contains("metadata"));
  const auto& type_info = (*var_decl)["metadata"]["type_info"];
  
  // Should resolve through 100-level chain
  EXPECT_EQ(type_info["declared_type"], "type_99");
  EXPECT_EQ(type_info["resolved_type"], "logic [7:0]");
  EXPECT_EQ(type_info["resolution_depth"], 100);
  EXPECT_EQ(type_info["base_type"], "logic");
  EXPECT_EQ(type_info["width"], 8);
}

}  // namespace
}  // namespace verilog

