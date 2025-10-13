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

// Phase 1: DPI-C Tests for JSON Export
// Tests for DPI-C (Direct Programming Interface) import/export

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

// Helper: Parse module and convert to JSON
json ParseModuleToJson(const std::string& code) {
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

// Test 1: Basic DPI-C import
TEST(DPITest, BasicImport) {
  const std::string code = R"(
module test;
  import "DPI-C" function int c_add(int a, int b);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty()) << "Parse should succeed";
  
  const json* dpi_import = FindNodeByTag(tree, "kDPIImportItem");
  ASSERT_NE(dpi_import, nullptr) << "Should find kDPIImportItem node";
  
  // Check for metadata
  if (dpi_import->contains("metadata") && (*dpi_import)["metadata"].contains("dpi_info")) {
    const auto& dpi_info = (*dpi_import)["metadata"]["dpi_info"];
    EXPECT_EQ(dpi_info["direction"], "import");
    EXPECT_EQ(dpi_info["spec"], "DPI-C");
    EXPECT_EQ(dpi_info["function_name"], "c_add");
  }
}

// Test 2: Import with parameters
TEST(DPITest, ImportWithParameters) {
  const std::string code = R"(
module test;
  import "DPI-C" function int c_calculate(int x, int y, int z);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* dpi_import = FindNodeByTag(tree, "kDPIImportItem");
  ASSERT_NE(dpi_import, nullptr);
}

// Test 3: Import with mixed parameter types
TEST(DPITest, ImportWithMixedTypes) {
  const std::string code = R"(
module test;
  import "DPI-C" function void c_display(string msg, int val, bit flag);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* dpi_import = FindNodeByTag(tree, "kDPIImportItem");
  ASSERT_NE(dpi_import, nullptr);
}

// Test 4: Import with context modifier
TEST(DPITest, ImportWithContext) {
  const std::string code = R"(
module test;
  import "DPI-C" context function void c_callback(int status);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* dpi_import = FindNodeByTag(tree, "kDPIImportItem");
  ASSERT_NE(dpi_import, nullptr);
  
  // Check for context flag in metadata
  if (dpi_import->contains("metadata") && (*dpi_import)["metadata"].contains("dpi_info")) {
    const auto& dpi_info = (*dpi_import)["metadata"]["dpi_info"];
    if (dpi_info.contains("is_context")) {
      EXPECT_TRUE(dpi_info["is_context"]);
    }
  }
}

// Test 5: Import with pure modifier
TEST(DPITest, ImportWithPure) {
  const std::string code = R"(
module test;
  import "DPI-C" pure function longint c_fast_mult(longint a, longint b);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* dpi_import = FindNodeByTag(tree, "kDPIImportItem");
  ASSERT_NE(dpi_import, nullptr);
  
  // Check for pure flag in metadata
  if (dpi_import->contains("metadata") && (*dpi_import)["metadata"].contains("dpi_info")) {
    const auto& dpi_info = (*dpi_import)["metadata"]["dpi_info"];
    if (dpi_info.contains("is_pure")) {
      EXPECT_TRUE(dpi_info["is_pure"]);
    }
  }
}

// Test 6: Import with no modifiers (simple function)
TEST(DPITest, ImportSimpleFunction) {
  const std::string code = R"(
module test;
  import "DPI-C" function void c_print(string msg);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* dpi_import = FindNodeByTag(tree, "kDPIImportItem");
  ASSERT_NE(dpi_import, nullptr);
}

// Test 7: Import task (void return)
TEST(DPITest, ImportTask) {
  const std::string code = R"(
module test;
  import "DPI-C" task c_wait_cycles(int n);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* dpi_import = FindNodeByTag(tree, "kDPIImportItem");
  ASSERT_NE(dpi_import, nullptr);
  
  // Check for is_task flag
  if (dpi_import->contains("metadata") && (*dpi_import)["metadata"].contains("dpi_info")) {
    const auto& dpi_info = (*dpi_import)["metadata"]["dpi_info"];
    if (dpi_info.contains("is_task")) {
      EXPECT_TRUE(dpi_info["is_task"]);
    }
  }
}

// Test 8: Import with complex types (logic, bit)
TEST(DPITest, ImportWithComplexTypes) {
  const std::string code = R"(
module test;
  import "DPI-C" function void c_process(logic [7:0] data, bit enable);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* dpi_import = FindNodeByTag(tree, "kDPIImportItem");
  ASSERT_NE(dpi_import, nullptr);
}

// Test 9: Import with array parameters
TEST(DPITest, ImportWithArrayParameters) {
  const std::string code = R"(
module test;
  import "DPI-C" function void c_array_process(int data[]);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* dpi_import = FindNodeByTag(tree, "kDPIImportItem");
  ASSERT_NE(dpi_import, nullptr);
}

// Test 10: Basic DPI-C export
TEST(DPITest, BasicExport) {
  const std::string code = R"(
module test;
  export "DPI-C" function sv_get_status;
  
  function int sv_get_status();
    return 42;
  endfunction
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* dpi_export = FindNodeByTag(tree, "kDPIExportItem");
  ASSERT_NE(dpi_export, nullptr) << "Should find kDPIExportItem node";
  
  // Check for metadata
  if (dpi_export->contains("metadata") && (*dpi_export)["metadata"].contains("dpi_info")) {
    const auto& dpi_info = (*dpi_export)["metadata"]["dpi_info"];
    EXPECT_EQ(dpi_info["direction"], "export");
    EXPECT_EQ(dpi_info["spec"], "DPI-C");
  }
}

// Test 11: Export with C name
TEST(DPITest, ExportWithCName) {
  const std::string code = R"(
module test;
  export "DPI-C" c_get_value = function sv_get_value;
  
  function int sv_get_value();
    return 100;
  endfunction
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* dpi_export = FindNodeByTag(tree, "kDPIExportItem");
  ASSERT_NE(dpi_export, nullptr);
  
  // Check for C linkage name in metadata
  if (dpi_export->contains("metadata") && (*dpi_export)["metadata"].contains("dpi_info")) {
    const auto& dpi_info = (*dpi_export)["metadata"]["dpi_info"];
    if (dpi_info.contains("c_linkage_name")) {
      EXPECT_EQ(dpi_info["c_linkage_name"], "c_get_value");
    }
  }
}

// Test 12: Export task
TEST(DPITest, ExportTask) {
  const std::string code = R"(
module test;
  export "DPI-C" task sv_wait;
  
  task sv_wait(int cycles);
    repeat(cycles) #10;
  endtask
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* dpi_export = FindNodeByTag(tree, "kDPIExportItem");
  ASSERT_NE(dpi_export, nullptr);
}

// Test 13: Multiple DPI imports
TEST(DPITest, MultipleImports) {
  const std::string code = R"(
module test;
  import "DPI-C" function int c_add(int a, int b);
  import "DPI-C" function int c_sub(int a, int b);
  import "DPI-C" function int c_mult(int a, int b);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count DPI imports
  int import_count = 0;
  std::function<void(const json&)> count_imports = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kDPIImportItem") {
      import_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_imports(child);
      }
    }
  };
  count_imports(tree);
  
  EXPECT_EQ(import_count, 3) << "Should find 3 DPI imports";
}

// Test 14: Multiple DPI exports
TEST(DPITest, MultipleExports) {
  const std::string code = R"(
module test;
  export "DPI-C" function sv_func1;
  export "DPI-C" function sv_func2;
  
  function int sv_func1();
    return 1;
  endfunction
  
  function int sv_func2();
    return 2;
  endfunction
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count DPI exports
  int export_count = 0;
  std::function<void(const json&)> count_exports = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kDPIExportItem") {
      export_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_exports(child);
      }
    }
  };
  count_exports(tree);
  
  EXPECT_EQ(export_count, 2) << "Should find 2 DPI exports";
}

// Test 15: Mixed imports and exports
TEST(DPITest, MixedImportsAndExports) {
  const std::string code = R"(
module test;
  import "DPI-C" function int c_external(int x);
  export "DPI-C" function sv_internal;
  
  function int sv_internal();
    return c_external(10);
  endfunction
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* dpi_import = FindNodeByTag(tree, "kDPIImportItem");
  const json* dpi_export = FindNodeByTag(tree, "kDPIExportItem");
  
  EXPECT_NE(dpi_import, nullptr) << "Should find import";
  EXPECT_NE(dpi_export, nullptr) << "Should find export";
}

// Test 16: DPI with system types (chandle)
TEST(DPITest, DPIWithSystemTypes) {
  const std::string code = R"(
module test;
  import "DPI-C" function chandle c_open_file(string filename);
  import "DPI-C" function void c_close_file(chandle handle);
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count DPI imports
  int import_count = 0;
  std::function<void(const json&)> count_imports = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kDPIImportItem") {
      import_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_imports(child);
      }
    }
  };
  count_imports(tree);
  
  EXPECT_EQ(import_count, 2) << "Should find 2 DPI imports with chandle";
}

// Test 17: Empty parameter list
TEST(DPITest, EmptyParameterList) {
  const std::string code = R"(
module test;
  import "DPI-C" function int c_get_random();
  import "DPI-C" function void c_initialize();
endmodule
)";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* dpi_import = FindNodeByTag(tree, "kDPIImportItem");
  ASSERT_NE(dpi_import, nullptr);
}

// Test 18: Performance test (50 DPI declarations)
TEST(DPITest, PerformanceTest) {
  std::string code = "module test;\n";
  
  // Generate 50 DPI imports
  for (int i = 0; i < 50; i++) {
    code += "  import \"DPI-C\" function int c_func" + std::to_string(i) + "(int x);\n";
  }
  
  code += "endmodule\n";
  
  json tree = ParseModuleToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count DPI imports
  int import_count = 0;
  std::function<void(const json&)> count_imports = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kDPIImportItem") {
      import_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_imports(child);
      }
    }
  };
  count_imports(tree);
  
  EXPECT_EQ(import_count, 50) << "Should find 50 DPI imports";
}

}  // namespace
}  // namespace verilog

