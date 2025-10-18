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

#include "verible/verilog/tools/semantic/json-exporter.h"

#include <memory>
#include <string>

#include "gtest/gtest.h"
#include "nlohmann/json.hpp"
#include "verible/verilog/analysis/call-graph-enhancer.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace {

// Helper to analyze code and build call graph
class JsonExporterTest : public ::testing::Test {
 protected:
  void SetUp() override {
    project_ = std::make_unique<VerilogProject>(".", std::vector<std::string>{});
    symbol_table_ = std::make_unique<SymbolTable>(nullptr);
  }

  std::unique_ptr<CallGraphEnhancer> AnalyzeCode(const std::string& code) {
    // Create in-memory source file
    auto source_file = std::make_unique<InMemoryVerilogSourceFile>("test.sv", code);
    const auto parse_status = source_file->Parse();
    if (!parse_status.ok()) {
      return nullptr;
    }

    // Build symbol table
    const auto build_diagnostics = 
        BuildSymbolTable(*source_file, symbol_table_.get(), nullptr);
    source_files_.push_back(std::move(source_file));

    // Build call graph
    auto cg = std::make_unique<CallGraphEnhancer>(*symbol_table_, *project_);
    const auto status = cg->BuildEnhancedCallGraph();
    if (!status.ok()) {
      return nullptr;
    }
    return cg;
  }

  std::unique_ptr<VerilogProject> project_;
  std::unique_ptr<SymbolTable> symbol_table_;
  std::vector<std::unique_ptr<InMemoryVerilogSourceFile>> source_files_;
};

TEST_F(JsonExporterTest, EmptyModule) {
  const char* code = R"(
    module empty;
    endmodule
  )";

  auto cg = AnalyzeCode(code);
  ASSERT_NE(cg, nullptr);

  SemanticJsonExporter exporter;
  std::string json_str = exporter.ExportCallGraph(*cg);

  // Parse JSON
  auto j = nlohmann::json::parse(json_str);

  // Verify structure
  EXPECT_TRUE(j.contains("call_graph"));
  EXPECT_TRUE(j["call_graph"].contains("nodes"));
  EXPECT_TRUE(j["call_graph"].contains("edges"));
  EXPECT_TRUE(j["call_graph"].contains("statistics"));

  // Empty module should have no functions
  EXPECT_EQ(j["call_graph"]["nodes"].size(), 0);
  EXPECT_EQ(j["call_graph"]["edges"].size(), 0);
}

TEST_F(JsonExporterTest, SingleFunction) {
  const char* code = R"(
    module test;
      function void simple();
      endfunction
    endmodule
  )";

  auto cg = AnalyzeCode(code);
  ASSERT_NE(cg, nullptr);

  SemanticJsonExporter exporter;
  std::string json_str = exporter.ExportCallGraph(*cg);

  // Parse JSON
  auto j = nlohmann::json::parse(json_str);

  // Should have one function node
  EXPECT_EQ(j["call_graph"]["nodes"].size(), 1);
  EXPECT_EQ(j["call_graph"]["nodes"][0]["name"], "simple");
  EXPECT_EQ(j["call_graph"]["nodes"][0]["type"], "function");
  // Single function with no callees is unreachable, not an entry point
  EXPECT_FALSE(j["call_graph"]["nodes"][0]["is_entry_point"].get<bool>());
  EXPECT_TRUE(j["call_graph"]["nodes"][0]["is_unreachable"].get<bool>());
  EXPECT_EQ(j["call_graph"]["nodes"][0]["call_depth"], 0);

  // No edges (no calls)
  EXPECT_EQ(j["call_graph"]["edges"].size(), 0);

  // Statistics
  EXPECT_EQ(j["call_graph"]["statistics"]["total_functions"], 1);
  EXPECT_EQ(j["call_graph"]["statistics"]["entry_points"], 0);
  EXPECT_EQ(j["call_graph"]["statistics"]["unreachable_functions"], 1);
}

TEST_F(JsonExporterTest, FunctionCallChain) {
  const char* code = R"(
    module test;
      function void caller();
        helper();
      endfunction
      
      function void helper();
      endfunction
    endmodule
  )";

  auto cg = AnalyzeCode(code);
  ASSERT_NE(cg, nullptr);

  SemanticJsonExporter exporter;
  std::string json_str = exporter.ExportCallGraph(*cg);

  // Parse JSON
  auto j = nlohmann::json::parse(json_str);

  // Should have two function nodes
  EXPECT_EQ(j["call_graph"]["nodes"].size(), 2);

  // Should have one edge (caller -> helper)
  EXPECT_EQ(j["call_graph"]["edges"].size(), 1);
  EXPECT_EQ(j["call_graph"]["edges"][0]["caller"], "caller");
  EXPECT_EQ(j["call_graph"]["edges"][0]["callee"], "helper");

  // Statistics
  EXPECT_EQ(j["call_graph"]["statistics"]["total_functions"], 2);
  EXPECT_EQ(j["call_graph"]["statistics"]["entry_points"], 1);
}

TEST_F(JsonExporterTest, TaskDetection) {
  const char* code = R"(
    module test;
      task my_task();
      endtask
    endmodule
  )";

  auto cg = AnalyzeCode(code);
  ASSERT_NE(cg, nullptr);

  SemanticJsonExporter exporter;
  std::string json_str = exporter.ExportCallGraph(*cg);

  // Parse JSON
  auto j = nlohmann::json::parse(json_str);

  // Should have one task node
  EXPECT_EQ(j["call_graph"]["nodes"].size(), 1);
  EXPECT_EQ(j["call_graph"]["nodes"][0]["name"], "my_task");
  EXPECT_EQ(j["call_graph"]["nodes"][0]["type"], "task");

  // Statistics
  EXPECT_EQ(j["call_graph"]["statistics"]["total_tasks"], 1);
  EXPECT_EQ(j["call_graph"]["statistics"]["total_functions"], 0);
}

TEST_F(JsonExporterTest, PrettyPrintControl) {
  const char* code = R"(
    module test;
      function void f();
      endfunction
    endmodule
  )";

  auto cg = AnalyzeCode(code);
  ASSERT_NE(cg, nullptr);

  // Test with pretty print
  SemanticJsonExporter exporter_pretty;
  exporter_pretty.SetPrettyPrint(true);
  std::string json_pretty = exporter_pretty.ExportCallGraph(*cg);
  EXPECT_TRUE(json_pretty.find("\n") != std::string::npos);  // Has newlines

  // Test without pretty print
  SemanticJsonExporter exporter_compact;
  exporter_compact.SetPrettyPrint(false);
  std::string json_compact = exporter_compact.ExportCallGraph(*cg);

  // Both should parse to same structure
  auto j_pretty = nlohmann::json::parse(json_pretty);
  auto j_compact = nlohmann::json::parse(json_compact);
  EXPECT_EQ(j_pretty, j_compact);
}

}  // namespace
}  // namespace verilog

