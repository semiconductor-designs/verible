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

// verible-verilog-semantic: Export Verible semantic analysis as JSON
//
// This tool analyzes SystemVerilog code and exports semantic information
// (call graphs, data flow, unused entities, module hierarchy) as JSON
// for consumption by external tools.
//
// Example usage:
//   verible-verilog-semantic design.sv
//   verible-verilog-semantic --output-file=output.json design.sv
//   verible-verilog-semantic --include-dataflow --include-unused design.sv

#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include "absl/flags/flag.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "nlohmann/json.hpp"
#include "verible/common/util/init-command-line.h"
#include "verible/verilog/analysis/call-graph-enhancer.h"
#include "verible/verilog/analysis/data-flow-analyzer.h"
#include "verible/verilog/analysis/enhanced-unused-detector.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/analysis/verilog-project.h"
#include "verible/verilog/tools/semantic/json-exporter.h"

ABSL_FLAG(std::string, output_file, "",
          "Output file for JSON (default: stdout)");
ABSL_FLAG(bool, pretty, true, "Pretty-print JSON output with indentation");
ABSL_FLAG(bool, include_callgraph, true, "Include call graph analysis");
ABSL_FLAG(bool, include_dataflow, false, "Include data flow analysis");
ABSL_FLAG(bool, include_unused, false, "Include unused entity detection");
ABSL_FLAG(bool, include_all, false, "Include all semantic analysis");

namespace verilog {
namespace {

// Analyze a single SystemVerilog file and export semantic information
absl::Status AnalyzeAndExport(absl::string_view filename) {
  // Create a VerilogProject and SymbolTable
  VerilogProject project(".", {});
  SymbolTable symbol_table(nullptr);

  // Read file contents
  std::string file_contents;
  std::ifstream ifs{std::string(filename)};
  if (!ifs) {
    return absl::Status(absl::StatusCode::kNotFound,
                        absl::StrCat("Failed to open file: ", filename));
  }
  file_contents.assign(std::istreambuf_iterator<char>{ifs},
                       std::istreambuf_iterator<char>{});

  // Create an in-memory source file for symbol table building
  auto source_file = std::make_unique<InMemoryVerilogSourceFile>(
      std::string(filename), file_contents);
  const auto parse_status = source_file->Parse();
  if (!parse_status.ok()) {
    return absl::Status(absl::StatusCode::kInvalidArgument,
                        absl::StrCat("Parse error: ", parse_status.message()));
  }

  // Build symbol table
  const auto build_diagnostics = BuildSymbolTable(*source_file, &symbol_table, nullptr);
  // Note: BuildSymbolTable returns a vector of diagnostics, not a status

  // Determine which analyzers to run
  bool run_callgraph = absl::GetFlag(FLAGS_include_callgraph) || absl::GetFlag(FLAGS_include_all);
  bool run_dataflow = absl::GetFlag(FLAGS_include_dataflow) || absl::GetFlag(FLAGS_include_all);
  bool run_unused = absl::GetFlag(FLAGS_include_unused) || absl::GetFlag(FLAGS_include_all);

  // Build combined JSON output
  nlohmann::json j;
  SemanticJsonExporter exporter;
  exporter.SetPrettyPrint(absl::GetFlag(FLAGS_pretty));

  // Run call graph analysis
  if (run_callgraph) {
    CallGraphEnhancer call_graph(symbol_table, project);
    const auto cg_status = call_graph.BuildEnhancedCallGraph();
    if (!cg_status.ok()) {
      return absl::Status(absl::StatusCode::kInternal,
                          absl::StrCat("Call graph build error: ", cg_status.message()));
    }
    std::string cg_json = exporter.ExportCallGraph(call_graph);
    auto cg_parsed = nlohmann::json::parse(cg_json);
    j["call_graph"] = cg_parsed["call_graph"];
  }

  // Run data flow analysis
  if (run_dataflow) {
    DataFlowAnalyzer dataflow(symbol_table, project);
    const auto df_status = dataflow.BuildDataFlowGraph();
    if (!df_status.ok()) {
      return absl::Status(absl::StatusCode::kInternal,
                          absl::StrCat("Data flow build error: ", df_status.message()));
    }
    std::string df_json = exporter.ExportDataFlow(dataflow);
    auto df_parsed = nlohmann::json::parse(df_json);
    j["data_flow"] = df_parsed["data_flow"];
  }

  // Run unused entity detection
  if (run_unused) {
    // Unused detection requires data flow analysis
    DataFlowAnalyzer dataflow(symbol_table, project);
    (void)dataflow.BuildDataFlowGraph();
    
    EnhancedUnusedDetector unused(dataflow, symbol_table);
    const auto unused_status = unused.AnalyzeUnusedEntities();
    if (!unused_status.ok()) {
      return absl::Status(absl::StatusCode::kInternal,
                          absl::StrCat("Unused detection error: ", unused_status.message()));
    }
    std::string unused_json = exporter.ExportUnused(unused);
    auto unused_parsed = nlohmann::json::parse(unused_json);
    j["unused"] = unused_parsed["unused"];
  }

  // Serialize final JSON
  std::string json_output;
  if (absl::GetFlag(FLAGS_pretty)) {
    json_output = j.dump(2);
  } else {
    json_output = j.dump();
  }

  // Output to file or stdout
  const std::string output_file = absl::GetFlag(FLAGS_output_file);
  if (output_file.empty()) {
    std::cout << json_output << std::endl;
  } else {
    std::ofstream ofs(output_file);
    if (!ofs) {
      return absl::Status(absl::StatusCode::kInternal,
                          absl::StrCat("Failed to write to file: ", output_file));
    }
    ofs << json_output << std::endl;
  }

  return absl::OkStatus();
}

}  // namespace
}  // namespace verilog

int main(int argc, char** argv) {
  const auto usage =
      "usage: verible-verilog-semantic [options] <file.sv>\n"
      "\n"
      "Analyzes SystemVerilog code and exports semantic information as JSON.\n"
      "\n"
      "Example:\n"
      "  verible-verilog-semantic design.sv\n"
      "  verible-verilog-semantic --output-file=output.json design.sv\n";

  const auto args = verible::InitCommandLine(usage, &argc, &argv);

  // args[0] is the program name, args[1] is the first file
  if (args.size() != 2) {
    std::cerr << "Error: Expected exactly one input file" << std::endl;
    std::cerr << usage << std::endl;
    return 1;
  }

  // args[1] is the filename
  const auto status = verilog::AnalyzeAndExport(args[1]);
  if (!status.ok()) {
    std::cerr << "Error: " << status.message() << std::endl;
    return 1;
  }

  return 0;
}

