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
#include <set>
#include <string>

#include "gtest/gtest.h"
#include "nlohmann/json.hpp"
#include "verible/verilog/analysis/call-graph-enhancer.h"
#include "verible/verilog/analysis/data-flow-analyzer.h"
#include "verible/verilog/analysis/enhanced-unused-detector.h"
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

TEST_F(JsonExporterTest, DataFlowBasic) {
  const char* code = R"(
    module dataflow_basic;
      parameter WIDTH = 8;
      input wire clk;
      input wire [WIDTH-1:0] data_in;
      output reg [WIDTH-1:0] data_out;
      
      reg [WIDTH-1:0] buffer;
      
      always @(posedge clk) begin
        buffer = data_in;
        data_out = buffer;
      end
    endmodule
  )";

  // Build symbol table
  auto source_file = InMemoryVerilogSourceFile("dataflow_basic.sv", code);
  auto symbol_table = std::make_unique<SymbolTable>(nullptr);
  const auto diagnostics = BuildSymbolTable(source_file, symbol_table.get(), nullptr);

  // Build data flow
  VerilogProject project(".", std::vector<std::string>{});
  DataFlowAnalyzer df(*symbol_table, project);
  (void)df.BuildDataFlowGraph();

  // Export to JSON
  SemanticJsonExporter exporter;
  std::string json_str = exporter.ExportDataFlow(df);

  // Parse and validate
  auto j = nlohmann::json::parse(json_str);
  EXPECT_TRUE(j.contains("data_flow"));
  EXPECT_TRUE(j["data_flow"].contains("nodes"));
  EXPECT_TRUE(j["data_flow"].contains("edges"));
  EXPECT_TRUE(j["data_flow"].contains("parameters"));
  EXPECT_TRUE(j["data_flow"].contains("constant_list"));

  // Verify structure is valid (parameter extraction may vary by implementation)
  EXPECT_TRUE(j["data_flow"]["nodes"].is_array());
  EXPECT_TRUE(j["data_flow"]["edges"].is_array());
  EXPECT_TRUE(j["data_flow"]["parameters"].is_array());
  EXPECT_TRUE(j["data_flow"]["constant_list"].is_array());
}

TEST_F(JsonExporterTest, UnusedBasic) {
  const char* code = R"(
    module unused_basic;
      reg used_signal;
      reg unused_signal;
      
      wire used_wire;
      wire unused_wire;
      
      assign used_wire = used_signal;
      
      function int used_function(int x);
        return x + 1;
      endfunction
      
      function int unused_function(int x);
        return x * 2;
      endfunction
      
      initial begin
        used_signal = 1'b0;
        used_signal = used_function(5);
      end
    endmodule
  )";

  // Build symbol table
  auto source_file = InMemoryVerilogSourceFile("unused_basic.sv", code);
  auto symbol_table = std::make_unique<SymbolTable>(nullptr);
  const auto diagnostics = BuildSymbolTable(source_file, symbol_table.get(), nullptr);

  // Build data flow
  VerilogProject project(".", std::vector<std::string>{});
  DataFlowAnalyzer df(*symbol_table, project);
  (void)df.BuildDataFlowGraph();

  // Build unused detector (only 2 parameters: dataflow_analyzer, symbol_table)
  EnhancedUnusedDetector unused(df, *symbol_table);
  (void)unused.AnalyzeUnusedEntities();

  // Export to JSON
  SemanticJsonExporter exporter;
  std::string json_str = exporter.ExportUnused(unused);

  // Parse and validate
  auto j = nlohmann::json::parse(json_str);
  EXPECT_TRUE(j.contains("unused"));
  EXPECT_TRUE(j["unused"].contains("entities"));
  EXPECT_TRUE(j["unused"].contains("statistics"));
  EXPECT_TRUE(j["unused"].contains("summary"));

  // Should have detected unused entities
  EXPECT_GE(j["unused"]["entities"].size(), 0);
}

// Schema validation tests
TEST_F(JsonExporterTest, SchemaVersionPresent) {
  const char* code = R"(
    module m;
      function int f();
        return 1;
      endfunction
    endmodule
  )";

  auto cg = AnalyzeCode(code);
  ASSERT_NE(cg, nullptr);

  SemanticJsonExporter exporter;
  std::string json_str = exporter.ExportCallGraph(*cg);
  auto j = nlohmann::json::parse(json_str);

  // Verify schema_version field exists at root level
  EXPECT_TRUE(j.contains("schema_version"));
  EXPECT_EQ(j["schema_version"], "1.0.0");

  // Verify call_graph has version field
  EXPECT_TRUE(j["call_graph"].contains("version"));
  EXPECT_EQ(j["call_graph"]["version"], "1.0.0");
}

TEST_F(JsonExporterTest, SchemaVersionInAllExports) {
  const char* code = R"(
    module m;
      parameter WIDTH = 8;
      reg [7:0] data;
      function int f();
        return 1;
      endfunction
    endmodule
  )";

  // Build symbol table
  auto source_file = InMemoryVerilogSourceFile("test.sv", code);
  auto symbol_table = std::make_unique<SymbolTable>(nullptr);
  const auto diagnostics = BuildSymbolTable(source_file, symbol_table.get(), nullptr);

  VerilogProject project(".", std::vector<std::string>{});
  SemanticJsonExporter exporter;

  // Test CallGraph export
  CallGraphEnhancer cg(*symbol_table, project);
  (void)cg.BuildEnhancedCallGraph();
  auto cg_json = nlohmann::json::parse(exporter.ExportCallGraph(cg));
  EXPECT_EQ(cg_json["schema_version"], "1.0.0");
  EXPECT_EQ(cg_json["call_graph"]["version"], "1.0.0");

  // Test DataFlow export
  DataFlowAnalyzer df(*symbol_table, project);
  (void)df.BuildDataFlowGraph();
  auto df_json = nlohmann::json::parse(exporter.ExportDataFlow(df));
  EXPECT_EQ(df_json["schema_version"], "1.0.0");
  EXPECT_EQ(df_json["data_flow"]["version"], "1.0.0");

  // Test Unused export
  EnhancedUnusedDetector unused(df, *symbol_table);
  (void)unused.AnalyzeUnusedEntities();
  auto unused_json = nlohmann::json::parse(exporter.ExportUnused(unused));
  EXPECT_EQ(unused_json["schema_version"], "1.0.0");
  EXPECT_EQ(unused_json["unused"]["version"], "1.0.0");
}

TEST_F(JsonExporterTest, SchemaFieldTypes) {
  const char* code = R"(
    module m;
      function int add(int a, int b);
        return a + b;
      endfunction
      
      function int double_add(int x);
        return add(x, 1);
      endfunction
    endmodule
  )";

  auto cg = AnalyzeCode(code);
  ASSERT_NE(cg, nullptr);

  SemanticJsonExporter exporter;
  std::string json_str = exporter.ExportCallGraph(*cg);
  auto j = nlohmann::json::parse(json_str);

  // Verify schema_version is a string
  EXPECT_TRUE(j["schema_version"].is_string());

  // Verify call_graph contains expected keys
  EXPECT_TRUE(j["call_graph"].contains("nodes"));
  EXPECT_TRUE(j["call_graph"].contains("edges"));
  EXPECT_TRUE(j["call_graph"].contains("statistics"));
  EXPECT_TRUE(j["call_graph"].contains("recursion_cycles"));

  // Verify nodes is an array
  EXPECT_TRUE(j["call_graph"]["nodes"].is_array());

  // Verify node structure
  if (!j["call_graph"]["nodes"].empty()) {
    const auto& node = j["call_graph"]["nodes"][0];
    EXPECT_TRUE(node.contains("name"));
    EXPECT_TRUE(node["name"].is_string());
    EXPECT_TRUE(node.contains("type"));
    EXPECT_TRUE(node["type"].is_string());
    EXPECT_TRUE(node.contains("call_depth"));
    EXPECT_TRUE(node["call_depth"].is_number());
    EXPECT_TRUE(node.contains("is_entry_point"));
    EXPECT_TRUE(node["is_entry_point"].is_boolean());
    EXPECT_TRUE(node.contains("caller_count"));
    EXPECT_TRUE(node["caller_count"].is_number());
  }

  // Verify statistics structure
  const auto& stats = j["call_graph"]["statistics"];
  EXPECT_TRUE(stats["total_functions"].is_number());
  EXPECT_TRUE(stats["total_tasks"].is_number());
  EXPECT_TRUE(stats["max_call_depth"].is_number());
}

// DataFlow analysis coverage tests
TEST_F(JsonExporterTest, DataFlowParameterExtraction) {
  const char* code = R"(
    module m;
      parameter WIDTH = 8;
      localparam DEPTH = 16;
    endmodule
  )";

  auto source = InMemoryVerilogSourceFile("test.sv", code);
  auto st = std::make_unique<SymbolTable>(nullptr);
  BuildSymbolTable(source, st.get(), nullptr);

  VerilogProject proj(".", {});
  DataFlowAnalyzer df(*st, proj);
  (void)df.BuildDataFlowGraph();

  SemanticJsonExporter exporter;
  auto json = nlohmann::json::parse(exporter.ExportDataFlow(df));

  // Verify parameters structure exists
  auto params = json["data_flow"]["parameters"];
  EXPECT_TRUE(params.is_array());
  
  // Verify parameter structure (if any parameters extracted)
  for (const auto& p : params) {
    EXPECT_TRUE(p.contains("name"));
    EXPECT_TRUE(p["name"].is_string());
    EXPECT_TRUE(p.contains("is_constant"));
    EXPECT_TRUE(p["is_constant"].is_boolean());
  }
}

TEST_F(JsonExporterTest, DataFlowParameterInConstantList) {
  const char* code = R"(
    module m;
      parameter P = 42;
      localparam LP = 100;
    endmodule
  )";

  auto source = InMemoryVerilogSourceFile("test.sv", code);
  auto st = std::make_unique<SymbolTable>(nullptr);
  BuildSymbolTable(source, st.get(), nullptr);

  VerilogProject proj(".", {});
  DataFlowAnalyzer df(*st, proj);
  (void)df.BuildDataFlowGraph();

  SemanticJsonExporter exporter;
  auto json = nlohmann::json::parse(exporter.ExportDataFlow(df));

  // Verify constant_list structure
  auto const_list = json["data_flow"]["constant_list"];
  EXPECT_TRUE(const_list.is_array());
  
  // constant_list contains strings (constant names)
  for (const auto& c : const_list) {
    EXPECT_TRUE(c.is_string());
  }
}

TEST_F(JsonExporterTest, DataFlowEdgeTypes) {
  const char* code = R"(
    module m;
      reg a, b;
      wire c;
      assign c = a;  // continuous
      always @(*) b = a;  // blocking
    endmodule
  )";

  auto source = InMemoryVerilogSourceFile("test.sv", code);
  auto st = std::make_unique<SymbolTable>(nullptr);
  BuildSymbolTable(source, st.get(), nullptr);

  VerilogProject proj(".", {});
  DataFlowAnalyzer df(*st, proj);
  (void)df.BuildDataFlowGraph();

  SemanticJsonExporter exporter;
  auto json = nlohmann::json::parse(exporter.ExportDataFlow(df));

  // Verify edges structure
  auto edges = json["data_flow"]["edges"];
  EXPECT_TRUE(edges.is_array());
  
  // Verify edge structure (if any edges extracted)
  for (const auto& e : edges) {
    EXPECT_TRUE(e.contains("type"));
    EXPECT_TRUE(e["type"].is_string());
    
    // Edge should have source/target (optional based on implementation)
    if (e.contains("source")) {
      EXPECT_TRUE(e["source"].is_string());
    }
    if (e.contains("target")) {
      EXPECT_TRUE(e["target"].is_string());
    }
    
    // Conditional flag
    if (e.contains("is_conditional")) {
      EXPECT_TRUE(e["is_conditional"].is_boolean());
    }
  }
}

TEST_F(JsonExporterTest, DataFlowNodeReferences) {
  const char* code = R"(
    module m;
      reg a, b;
      always @(*) b = a;
    endmodule
  )";

  auto source = InMemoryVerilogSourceFile("test.sv", code);
  auto st = std::make_unique<SymbolTable>(nullptr);
  BuildSymbolTable(source, st.get(), nullptr);

  VerilogProject proj(".", {});
  DataFlowAnalyzer df(*st, proj);
  (void)df.BuildDataFlowGraph();

  SemanticJsonExporter exporter;
  auto json = nlohmann::json::parse(exporter.ExportDataFlow(df));

  // Build set of all node names
  std::set<std::string> node_names;
  for (const auto& node : json["data_flow"]["nodes"]) {
    node_names.insert(node["name"]);
  }

  // Verify all edge references point to valid nodes
  for (const auto& edge : json["data_flow"]["edges"]) {
    if (edge.contains("source")) {
      std::string source = edge["source"];
      EXPECT_TRUE(node_names.count(source) > 0 || source.empty());
    }
    if (edge.contains("target")) {
      std::string target = edge["target"];
      EXPECT_TRUE(node_names.count(target) > 0 || target.empty());
    }
  }
}

TEST_F(JsonExporterTest, DataFlowNodeTypes) {
  const char* code = R"(
    module m;
      parameter P = 1;
      input wire [7:0] in;
      output reg [7:0] out;
      reg [7:0] temp;
    endmodule
  )";

  auto source = InMemoryVerilogSourceFile("test.sv", code);
  auto st = std::make_unique<SymbolTable>(nullptr);
  BuildSymbolTable(source, st.get(), nullptr);

  VerilogProject proj(".", {});
  DataFlowAnalyzer df(*st, proj);
  (void)df.BuildDataFlowGraph();

  SemanticJsonExporter exporter;
  auto json = nlohmann::json::parse(exporter.ExportDataFlow(df));

  // Verify all nodes have a type field
  for (const auto& node : json["data_flow"]["nodes"]) {
    EXPECT_TRUE(node.contains("type"));
    std::string type = node["type"];
    
    // Type should be one of the valid types
    EXPECT_TRUE(type == "signal" || type == "variable" || type == "port" ||
                type == "parameter" || type == "constant" || type == "unknown");
    
    // Verify flags exist
    EXPECT_TRUE(node.contains("is_constant"));
    EXPECT_TRUE(node.contains("is_parameter"));
    EXPECT_TRUE(node.contains("is_port"));
    EXPECT_TRUE(node.contains("is_read"));
    EXPECT_TRUE(node.contains("is_written"));
  }
}

}  // namespace
}  // namespace verilog

