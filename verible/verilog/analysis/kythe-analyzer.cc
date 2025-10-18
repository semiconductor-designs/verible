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

#include "verible/verilog/analysis/kythe-analyzer.h"

#include <chrono>
#include <memory>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"
#include "verible/verilog/tools/kythe/indexing-facts-tree.h"
#include "verible/verilog/tools/kythe/indexing-facts-tree-extractor.h"
#include "verible/verilog/tools/kythe/kythe-facts.h"
#include "verible/verilog/tools/kythe/kythe-facts-extractor.h"

namespace verilog {

// Pimpl implementation to hide Kythe internals
struct KytheAnalyzer::KytheInternals {
  // Kythe data structures
  // Note: IndexingNodeData requires an IndexingFactType, using kFile as default
  kythe::IndexingFactNode facts_tree{kythe::IndexingNodeData(IndexingFactType::kFile)};
  
  // Conversion helpers
  static SourceLocation ConvertKytheAnchorToSourceLocation(
      absl::string_view file_path,
      int byte_start,
      int byte_end,
      absl::string_view file_content);
  
  static void ExtractVariableNameFromSignature(
      absl::string_view signature,
      std::string* simple_name,
      std::string* fully_qualified_name);
};

SourceLocation KytheAnalyzer::KytheInternals::ConvertKytheAnchorToSourceLocation(
    absl::string_view file_path,
    int byte_start,
    int byte_end,
    absl::string_view file_content) {
  SourceLocation loc;
  loc.file_path = std::string(file_path);
  loc.byte_start = byte_start;
  loc.byte_end = byte_end;
  
  // Convert byte offset to line:column
  if (byte_start >= 0 && byte_start < static_cast<int>(file_content.size())) {
    int line = 1;
    int column = 1;
    for (int i = 0; i < byte_start; ++i) {
      if (file_content[i] == '\n') {
        ++line;
        column = 1;
      } else {
        ++column;
      }
    }
    loc.line = line;
    loc.column = column;
  }
  
  return loc;
}

void KytheAnalyzer::KytheInternals::ExtractVariableNameFromSignature(
    absl::string_view signature,
    std::string* simple_name,
    std::string* fully_qualified_name) {
  // Kythe signature format: "path/file.sv#scope#variable#"
  // Example: "/tmp/test.sv#module#signal#"
  
  *fully_qualified_name = std::string(signature);
  
  // Extract simple name (last component before final '#')
  size_t last_hash = signature.rfind('#');
  if (last_hash != absl::string_view::npos && last_hash > 0) {
    size_t prev_hash = signature.rfind('#', last_hash - 1);
    if (prev_hash != absl::string_view::npos) {
      *simple_name = std::string(
          signature.substr(prev_hash + 1, last_hash - prev_hash - 1));
    } else {
      *simple_name = std::string(signature.substr(0, last_hash));
    }
  } else {
    *simple_name = std::string(signature);
  }
}

KytheAnalyzer::KytheAnalyzer(const SymbolTable& symbol_table,
                             const VerilogProject& project)
    : symbol_table_(&symbol_table),
      project_(&project),
      analyzed_(false),
      internals_(std::make_unique<KytheInternals>()) {
  // symbol_table_ will be used for scope resolution in future implementation
  (void)symbol_table_;  // Suppress unused warning
}

KytheAnalyzer::~KytheAnalyzer() = default;

KytheAnalyzer::KytheAnalyzer(KytheAnalyzer&&) noexcept = default;
KytheAnalyzer& KytheAnalyzer::operator=(KytheAnalyzer&&) noexcept = default;

absl::Status KytheAnalyzer::BuildKytheFacts() {
  auto start_time = std::chrono::steady_clock::now();
  
  // Clear previous results
  Clear();
  
  try {
    // Step 1: Extract Kythe facts from the project
    std::vector<std::string> file_paths;
    for (const auto& file_entry : *project_) {
      file_paths.push_back(std::string(file_entry.first));
    }
    
    if (file_paths.empty()) {
      return absl::InvalidArgumentError("No files to analyze");
    }
    
    statistics_.files_analyzed = file_paths.size();
    
    // Create a temporary file list for Kythe extraction
    // Note: Kythe extractor expects a file_list_path, but we'll use the
    // in-memory project instead
    std::vector<absl::Status> errors;
    internals_->facts_tree = kythe::ExtractFiles(
        /* file_list_path= */ "",
        const_cast<VerilogProject*>(project_),
        file_paths,
        &errors);
    
    // Check for extraction errors
    if (!errors.empty()) {
      std::string error_msg = "Kythe extraction errors:\n";
      for (const auto& err : errors) {
        absl::StrAppend(&error_msg, "  - ", err.message(), "\n");
      }
      return absl::InternalError(error_msg);
    }
    
    // Step 2: Process the facts tree to extract variable references
    // This is a simplified extraction - we'll traverse the tree and collect
    // variable reference facts
    
    // For now, create a stub that will be filled in iteratively via TDD
    // TODO: Implement traversal and edge extraction
    
    statistics_.total_facts = 1;  // Placeholder
    statistics_.total_edges = 0;  // Placeholder
    
    analyzed_ = true;
    
    auto end_time = std::chrono::steady_clock::now();
    statistics_.analysis_time_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
        end_time - start_time).count();
    
    return absl::OkStatus();
  } catch (const std::exception& e) {
    return absl::InternalError(
        absl::StrCat("Kythe analysis failed: ", e.what()));
  }
}

const std::vector<VariableReference>& KytheAnalyzer::GetVariableReferences() const {
  return variable_references_;
}

const std::vector<VariableDefinition>& KytheAnalyzer::GetVariableDefinitions() const {
  return variable_definitions_;
}

const KytheStatistics& KytheAnalyzer::GetStatistics() const {
  return statistics_;
}

void KytheAnalyzer::Clear() {
  variable_references_.clear();
  variable_definitions_.clear();
  statistics_.Clear();
  analyzed_ = false;
}

bool KytheAnalyzer::IsAnalyzed() const {
  return analyzed_;
}

}  // namespace verilog

