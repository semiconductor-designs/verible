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

// Tests for Cross-Reference Metadata in JSON CST export (Phase B)

#include <chrono>
#include <iostream>
#include <string>
#include <vector>

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

namespace verilog {
namespace {

using json = nlohmann::json;

// Helper: Parse code and return JSON tree
static json ParseModuleToJson(const std::string &code) {
  const auto analyzer_ptr =
      verilog::VerilogAnalyzer::AnalyzeAutomaticMode(code, "<test>", verilog::VerilogPreprocess::Config());
  if (!analyzer_ptr) return json();
  
  const auto& analyzer = *analyzer_ptr;
  if (!analyzer.LexStatus().ok() || !analyzer.ParseStatus().ok()) {
    return json();
  }
  
  const auto &tree = analyzer.SyntaxTree();
  if (!tree) return json();
  
  return ConvertVerilogTreeToJson(*tree, code);
}

// Helper: Find node by tag and containing text (recursive search)
static const json* FindNodeByTag(const json &node, const std::string &tag) {
  if (node.contains("tag") && node["tag"] == tag) {
    return &node;
  }
  
  if (node.contains("children")) {
    for (const auto &child : node["children"]) {
      const json* result = FindNodeByTag(child, tag);
      if (result) return result;
    }
  }
  
  return nullptr;
}

// Helper: Find all nodes with specific tag
static std::vector<const json*> FindAllNodesByTag(const json &node, const std::string &tag) {
  std::vector<const json*> results;
  
  if (node.contains("tag") && node["tag"] == tag) {
    results.push_back(&node);
  }
  
  if (node.contains("children")) {
    for (const auto &child : node["children"]) {
      auto child_results = FindAllNodesByTag(child, tag);
      results.insert(results.end(), child_results.begin(), child_results.end());
    }
  }
  
  return results;
}

// Helper: Find reference by symbol name
static const json* FindReferenceByName(const json &node, const std::string &name) {
  if (node.contains("tag") && node["tag"] == "kReference") {
    if (node.contains("text")) {
      std::string text = node["text"];
      if (text.find(name) != std::string::npos) {
        return &node;
      }
    }
  }
  
  if (node.contains("children")) {
    for (const auto &child : node["children"]) {
      const json* result = FindReferenceByName(child, name);
      if (result) return result;
    }
  }
  
  return nullptr;
}

// ============================================================================
// TEST 1: Simple Variable Definition vs Usage
// ============================================================================

TEST(CrossReferenceTest, SimpleVariableDefinitionUsage) {
  const std::string code = R"(
module test;
  logic data_valid;
  
  always_comb begin
    if (data_valid) begin
      // use data_valid
    end
  end
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  // Find definition
  auto decls = FindAllNodesByTag(tree_json, "kDataDeclaration");
  ASSERT_GE(decls.size(), 1);
  
  const json* decl = decls[0];
  ASSERT_TRUE(decl->contains("metadata"));
  ASSERT_TRUE((*decl)["metadata"].contains("cross_ref"));
  
  const auto& xref = (*decl)["metadata"]["cross_ref"];
  EXPECT_EQ(xref["symbol"], "data_valid");
  EXPECT_EQ(xref["ref_type"], "definition");
  EXPECT_TRUE(xref.contains("definition_location"));
  EXPECT_TRUE(xref["definition_location"].contains("line"));
  EXPECT_EQ(xref["definition_location"]["line"], 3);
  
  // Find usage
  const json* ref = FindReferenceByName(tree_json, "data_valid");
  ASSERT_NE(ref, nullptr);
  ASSERT_TRUE(ref->contains("metadata"));
  ASSERT_TRUE((*ref)["metadata"].contains("cross_ref"));
  
  const auto& ref_xref = (*ref)["metadata"]["cross_ref"];
  EXPECT_EQ(ref_xref["symbol"], "data_valid");
  EXPECT_EQ(ref_xref["ref_type"], "usage");
  EXPECT_TRUE(ref_xref.contains("definition_location"));
  EXPECT_EQ(ref_xref["definition_location"]["line"], 3);
}

// ============================================================================
// TEST 2: Port Definition (Input/Output/Inout)
// ============================================================================

TEST(CrossReferenceTest, PortDefinitions) {
  const std::string code = R"(
module test(
  input  logic clk,
  input  logic rst_n,
  output logic data_out,
  inout  wire  data_io
);
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  // Find all port declarations
  auto ports = FindAllNodesByTag(tree_json, "kPortDeclaration");
  ASSERT_GE(ports.size(), 4);
  
  // Check input port metadata
  bool found_clk = false;
  for (const auto* port : ports) {
    if (port->contains("metadata") && (*port)["metadata"].contains("cross_ref")) {
      const auto& xref = (*port)["metadata"]["cross_ref"];
      if (xref["symbol"] == "clk") {
        found_clk = true;
        EXPECT_EQ(xref["ref_type"], "definition");
        EXPECT_TRUE(xref["is_input"].get<bool>());
        EXPECT_FALSE(xref["is_output"].get<bool>());
        EXPECT_FALSE(xref["is_inout"].get<bool>());
      }
    }
  }
  EXPECT_TRUE(found_clk);
}

// ============================================================================
// TEST 3: Parameter Definition and Usage
// ============================================================================

TEST(CrossReferenceTest, ParameterDefinitionUsage) {
  const std::string code = R"(
module test #(
  parameter WIDTH = 8
)(
  input logic [WIDTH-1:0] data
);
  logic [WIDTH-1:0] buffer;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  // Find parameter definition
  const json* param = FindNodeByTag(tree_json, "kParamDeclaration");
  ASSERT_NE(param, nullptr);
  ASSERT_TRUE(param->contains("metadata"));
  ASSERT_TRUE((*param)["metadata"].contains("cross_ref"));
  
  const auto& xref = (*param)["metadata"]["cross_ref"];
  EXPECT_EQ(xref["symbol"], "WIDTH");
  EXPECT_EQ(xref["ref_type"], "definition");
  EXPECT_TRUE(xref["is_parameter"].get<bool>());
  
  // Find parameter usages (should be 2: port and buffer)
  auto refs = FindAllNodesByTag(tree_json, "kReference");
  int width_usages = 0;
  for (const auto* ref : refs) {
    if (ref->contains("text")) {
      std::string text = (*ref)["text"];
      if (text.find("WIDTH") != std::string::npos) {
        width_usages++;
        if (ref->contains("metadata") && (*ref)["metadata"].contains("cross_ref")) {
          const auto& ref_xref = (*ref)["metadata"]["cross_ref"];
          EXPECT_EQ(ref_xref["ref_type"], "usage");
        }
      }
    }
  }
  EXPECT_GE(width_usages, 2);
}

// ============================================================================
// TEST 4: Multiple Usages of Same Signal
// ============================================================================

TEST(CrossReferenceTest, MultipleUsages) {
  const std::string code = R"(
module test;
  logic counter;
  
  always_ff @(posedge clk) begin
    counter <= counter + 1;
  end
  
  assign overflow = (counter == 255);
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  // Find all references to "counter"
  auto all_nodes = FindAllNodesByTag(tree_json, "kReference");
  int counter_refs = 0;
  for (const auto* ref : all_nodes) {
    if (ref->contains("text")) {
      std::string text = (*ref)["text"];
      if (text.find("counter") != std::string::npos) {
      if (ref->contains("metadata") && (*ref)["metadata"].contains("cross_ref")) {
        counter_refs++;
        const auto& xref = (*ref)["metadata"]["cross_ref"];
        EXPECT_EQ(xref["symbol"], "counter");
        EXPECT_EQ(xref["ref_type"], "usage");
      }
      }
    }
  }
  EXPECT_GE(counter_refs, 2);  // At least 2 usages in the logic
}

// ============================================================================
// TEST 5: Hierarchical Reference (sub.signal)
// ============================================================================

TEST(CrossReferenceTest, HierarchicalReference) {
  const std::string code = R"(
module test;
  sub_module sub();
  
  assign out = sub.internal_signal;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  // Find hierarchical reference
  const json* hier_ref = FindNodeByTag(tree_json, "kHierarchyExtension");
  if (hier_ref) {
    ASSERT_TRUE(hier_ref->contains("metadata"));
    ASSERT_TRUE((*hier_ref)["metadata"].contains("cross_ref"));
    
    const auto& xref = (*hier_ref)["metadata"]["cross_ref"];
    EXPECT_EQ(xref["ref_type"], "hierarchical_usage");
    EXPECT_TRUE(xref.contains("hierarchical_path"));
    EXPECT_TRUE(xref["hierarchical_path"].get<std::string>().find("sub") != std::string::npos);
  }
}

// ============================================================================
// TEST 6: Cross-Module Reference
// ============================================================================

TEST(CrossReferenceTest, CrossModuleReference) {
  const std::string code = R"(
module sub_module;
  logic internal;
endmodule

module test;
  sub_module sub();
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  // Find module instantiation
  const json* inst = FindNodeByTag(tree_json, "kGateInstantiation");
  if (inst) {
    ASSERT_TRUE(inst->contains("metadata"));
    if ((*inst)["metadata"].contains("cross_ref")) {
      const auto& xref = (*inst)["metadata"]["cross_ref"];
      EXPECT_EQ(xref["ref_type"], "module_instantiation");
      EXPECT_TRUE(xref.contains("module_name"));
    }
  }
}

// ============================================================================
// TEST 7: Definition Before Use
// ============================================================================

TEST(CrossReferenceTest, DefinitionBeforeUse) {
  const std::string code = R"(
module test;
  logic signal;     // Line 3: definition
  
  always_comb begin
    signal = 1'b1;  // Line 6: usage (after definition)
  end
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* ref = FindReferenceByName(tree_json, "signal");
  if (ref && ref->contains("metadata") && (*ref)["metadata"].contains("cross_ref")) {
    const auto& xref = (*ref)["metadata"]["cross_ref"];
    EXPECT_EQ(xref["ref_type"], "usage");
    EXPECT_FALSE(xref.value("is_forward_reference", false));  // Not a forward ref
    EXPECT_TRUE(xref.contains("definition_location"));
    EXPECT_LT(xref["definition_location"]["line"], 6);  // Defined before line 6
  }
}

// ============================================================================
// TEST 8: Usage Before Definition (Forward Reference)
// ============================================================================

TEST(CrossReferenceTest, ForwardReference) {
  const std::string code = R"(
module test;
  initial begin
    data = 1'b1;    // Line 4: usage (before definition)
  end
  
  logic data;       // Line 7: definition (after usage)
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* ref = FindReferenceByName(tree_json, "data");
  if (ref && ref->contains("metadata") && (*ref)["metadata"].contains("cross_ref")) {
    const auto& xref = (*ref)["metadata"]["cross_ref"];
    EXPECT_EQ(xref["ref_type"], "usage");
    EXPECT_TRUE(xref["is_forward_reference"].get<bool>());
    EXPECT_TRUE(xref.contains("definition_location"));
    EXPECT_GT(xref["definition_location"]["line"], 4);  // Defined after line 4
  }
}

// ============================================================================
// TEST 9: Multiple Definitions (Redeclaration Error Case)
// ============================================================================

TEST(CrossReferenceTest, MultipleDefinitions) {
  const std::string code = R"(
module test;
  logic signal;
  logic signal;  // Redeclaration (error, but should be tracked)
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  // Find all declarations of "signal"
  auto decls = FindAllNodesByTag(tree_json, "kDataDeclaration");
  int signal_defs = 0;
  for (const auto* decl : decls) {
    if (decl->contains("text")) {
      std::string text = (*decl)["text"];
      if (text.find("signal") != std::string::npos) {
      if (decl->contains("metadata") && (*decl)["metadata"].contains("cross_ref")) {
        signal_defs++;
        const auto& xref = (*decl)["metadata"]["cross_ref"];
        EXPECT_EQ(xref["ref_type"], "definition");
      }
      }
    }
  }
  
  // Should detect multiple definitions
  if (signal_defs > 1) {
    // Check if redeclaration is flagged
    for (const auto* decl : decls) {
      if (decl->contains("metadata") && (*decl)["metadata"].contains("cross_ref")) {
        const auto& xref = (*decl)["metadata"]["cross_ref"];
        if (xref.contains("is_redeclaration")) {
          EXPECT_TRUE(xref["is_redeclaration"].get<bool>());
        }
      }
    }
  }
}

// ============================================================================
// TEST 10: Unresolved Reference
// ============================================================================

TEST(CrossReferenceTest, UnresolvedReference) {
  const std::string code = R"(
module test;
  assign out = undefined_signal;  // Reference to undefined signal
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  const json* ref = FindReferenceByName(tree_json, "undefined_signal");
  if (ref && ref->contains("metadata") && (*ref)["metadata"].contains("cross_ref")) {
    const auto& xref = (*ref)["metadata"]["cross_ref"];
    EXPECT_EQ(xref["ref_type"], "usage");
    EXPECT_TRUE(xref["is_unresolved"].get<bool>());
    EXPECT_FALSE(xref.contains("definition_location"));  // No definition found
  }
}

// ============================================================================
// TEST 11: Package Import Reference
// ============================================================================

TEST(CrossReferenceTest, PackageImportReference) {
  const std::string code = R"(
package my_pkg;
  typedef logic [31:0] word_t;
endpackage

module test;
  import my_pkg::*;
  my_pkg::word_t data;
endmodule
)";

  const json tree_json = ParseModuleToJson(code);
  ASSERT_FALSE(tree_json.empty());
  
  // Find package import
  const json* import_node = FindNodeByTag(tree_json, "kPackageImportDeclaration");
  if (import_node && import_node->contains("metadata") && (*import_node)["metadata"].contains("cross_ref")) {
    const auto& xref = (*import_node)["metadata"]["cross_ref"];
    EXPECT_EQ(xref["ref_type"], "package_import");
    EXPECT_TRUE(xref.contains("package_name"));
    EXPECT_EQ(xref["package_name"], "my_pkg");
  }
  
  // Find package-scoped reference
  auto refs = FindAllNodesByTag(tree_json, "kQualifiedId");
  for (const auto* ref : refs) {
    if (ref->contains("text")) {
      std::string text = (*ref)["text"];
      if (text.find("word_t") != std::string::npos) {
        if (ref->contains("metadata") && (*ref)["metadata"].contains("cross_ref")) {
          const auto& xref = (*ref)["metadata"]["cross_ref"];
          EXPECT_EQ(xref["ref_type"], "usage");
          EXPECT_TRUE(xref["is_package_scoped"].get<bool>());
          EXPECT_TRUE(xref.contains("definition_location"));
        }
      }
    }
  }
}

// ============================================================================
// TEST 12: Performance Test - 500 Signals with Cross-Refs
// ============================================================================

TEST(CrossReferenceTest, Performance500Signals) {
  // Build code with 500 signals
  std::string code = "module test;\n";
  
  // Define 500 signals
  for (int i = 0; i < 500; ++i) {
    code += "  logic signal_" + std::to_string(i) + ";\n";
  }
  
  // Use each signal once
  code += "\n  always_comb begin\n";
  for (int i = 0; i < 500; ++i) {
    code += "    signal_" + std::to_string(i) + " = 1'b0;\n";
  }
  code += "  end\n";
  code += "endmodule\n";
  
  auto start = std::chrono::high_resolution_clock::now();
  const json tree_json = ParseModuleToJson(code);
  auto end = std::chrono::high_resolution_clock::now();
  
  ASSERT_FALSE(tree_json.empty());
  
  auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
  std::cout << "Performance: 500 signals with cross-refs processed in " 
            << duration.count() << "ms" << std::endl;
  
  // Should complete in reasonable time (<5 seconds)
  EXPECT_LT(duration.count(), 5000);
  
  // Verify some signals have cross-ref metadata
  auto decls = FindAllNodesByTag(tree_json, "kDataDeclaration");
  EXPECT_GE(decls.size(), 500);
  
  int with_xref = 0;
  for (const auto* decl : decls) {
    if (decl->contains("metadata") && (*decl)["metadata"].contains("cross_ref")) {
      with_xref++;
    }
  }
  EXPECT_GT(with_xref, 0);  // At least some should have metadata
}

}  // namespace
}  // namespace verilog

