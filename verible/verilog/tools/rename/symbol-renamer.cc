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

#include "verible/verilog/tools/rename/symbol-renamer.h"

#include <algorithm>
#include <cctype>
#include <fstream>
#include <map>
#include <set>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "verible/common/text/token-info.h"
#include "verible/common/text/symbol.h"
#include "verible/common/text/text-structure.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-inference.h"
#include "verible/verilog/analysis/verilog-project.h"
#include "verible/verilog/parser/verilog-token-enum.h"

namespace verilog {
namespace tools {

// SystemVerilog reserved keywords that cannot be used as identifiers
static const std::set<std::string> kReservedKeywords = {
    "module", "endmodule", "function", "endfunction", "task", "endtask",
    "begin", "end", "if", "else", "case", "endcase", "for", "while",
    "logic", "wire", "reg", "input", "output", "inout", "parameter",
    "localparam", "assign", "always", "initial", "generate", "endgenerate",
    "class", "endclass", "package", "endpackage", "interface", "endinterface"
};

SymbolRenamer::SymbolRenamer(const verilog::SymbolTable* symbol_table,
                             const verilog::analysis::TypeInference* type_inference)
    : symbol_table_(symbol_table), type_inference_(type_inference) {}

std::vector<verible::TokenInfo> SymbolRenamer::FindReferences(
    const std::string& symbol_name,
    const verible::Symbol& scope) {
  std::vector<verible::TokenInfo> references;
  
  if (!symbol_table_) return references;
  
  const auto* project = symbol_table_->Project();
  if (!project) return references;
  
  // Iterate through all translation units in the project
  for (const auto& translation_unit : *project) {
    const auto* source = translation_unit.second.get();
    if (!source) continue;
    
    const auto* text_structure = source->GetTextStructure();
    if (!text_structure) continue;
    
    const auto& tokens = text_structure->TokenStream();
    
    // Traverse all tokens looking for matching identifiers
    for (const auto& token : tokens) {
      // Check if token is an identifier (not a keyword)
      if (token.token_enum() == SymbolIdentifier) {
        if (token.text() == symbol_name) {
          references.push_back(token);
        }
      }
    }
  }
  
  return references;
}

absl::Status SymbolRenamer::ValidateRename(const std::string& old_name,
                                            const std::string& new_name,
                                            const verible::Symbol& scope) {
  // Basic validation
  if (old_name.empty()) {
    return absl::InvalidArgumentError("Old name cannot be empty");
  }
  
  if (new_name.empty()) {
    return absl::InvalidArgumentError("New name cannot be empty");
  }
  
  if (old_name == new_name) {
    return absl::InvalidArgumentError("Old and new names are identical");
  }
  
  // Check if new_name is a reserved keyword
  if (kReservedKeywords.count(new_name) > 0) {
    return absl::InvalidArgumentError(
        absl::StrCat("'", new_name, "' is a reserved keyword"));
  }
  
  // Validate identifier format (must start with letter or underscore)
  if (!new_name.empty()) {
    char first = new_name[0];
    if (!std::isalpha(first) && first != '_') {
      return absl::InvalidArgumentError(
          "Identifier must start with letter or underscore");
    }
    
    // Check all characters are alphanumeric or underscore
    for (char c : new_name) {
      if (!std::isalnum(c) && c != '_') {
        return absl::InvalidArgumentError(
            "Identifier can only contain letters, digits, and underscores");
      }
    }
  }
  
  // Check if old_name exists (only if we have a project with files)
  if (symbol_table_ && symbol_table_->Project()) {
    const auto* project = symbol_table_->Project();
    bool has_files = false;
    for (const auto& _ : *project) {
      has_files = true;
      break;
    }
    
    if (has_files) {
      auto refs = FindReferences(old_name, scope);
      if (refs.empty()) {
        return absl::NotFoundError(
            absl::StrCat("Symbol '", old_name, "' not found in scope"));
      }
      
      // Check if new_name would conflict
      auto conflicts = FindReferences(new_name, scope);
      if (!conflicts.empty()) {
        return absl::AlreadyExistsError(
            absl::StrCat("Symbol '", new_name, "' already exists in scope"));
      }
    }
  }
  
  return absl::OkStatus();
}

absl::StatusOr<RenameReport> SymbolRenamer::Rename(
    const std::string& old_name,
    const std::string& new_name,
    const verible::Symbol& scope,
    bool dry_run) {
  // Validate rename first
  auto validation_status = ValidateRename(old_name, new_name, scope);
  if (!validation_status.ok()) {
    return validation_status;
  }
  
  // Find all references
  auto refs = FindReferences(old_name, scope);
  
  RenameReport report;
  report.occurrences_renamed = refs.size();
  
  if (!symbol_table_ || refs.empty()) {
    report.summary = absl::StrCat(
        "Would rename '", old_name, "' to '", new_name, "' (0 occurrences)");
    return report;
  }
  
  const auto* project = symbol_table_->Project();
  if (!project) {
    report.summary = "No project available for file modification";
    return report;
  }
  
  // Group references by file
  std::map<std::string, std::vector<verible::TokenInfo>> refs_by_file;
  for (const auto& translation_unit : *project) {
    const auto* source = translation_unit.second.get();
    if (!source) continue;
    
    const auto* text_structure = source->GetTextStructure();
    if (!text_structure) continue;
    
    const std::string_view base = text_structure->Contents();
    
    for (const auto& ref : refs) {
      // Check if this token belongs to this file
      if (ref.text().data() >= base.data() &&
          ref.text().data() < base.data() + base.size()) {
        refs_by_file[std::string(source->ResolvedPath())].push_back(ref);
      }
    }
  }
  
  report.files_modified = refs_by_file.size();
  
  if (dry_run) {
    report.summary = absl::StrCat(
        "Would rename '", old_name, "' to '", new_name, "': ",
        report.occurrences_renamed, " occurrences in ",
        report.files_modified, " file(s)");
    for (const auto& entry : refs_by_file) {
      report.modified_files.push_back(entry.first);
    }
    return report;
  }
  
  // Actually perform the rename
  for (const auto& entry : refs_by_file) {
    const std::string& filename = entry.first;
    const auto& file_refs = entry.second;
    
    // Read file content
    std::ifstream input(filename);
    if (!input.is_open()) {
      return absl::InternalError(
          absl::StrCat("Failed to open file for reading: ", filename));
    }
    std::string content((std::istreambuf_iterator<char>(input)),
                         std::istreambuf_iterator<char>());
    input.close();
    
    // Create backup
    std::string backup_filename = filename + ".bak";
    std::ofstream backup(backup_filename);
    if (!backup.is_open()) {
      return absl::InternalError(
          absl::StrCat("Failed to create backup file: ", backup_filename));
    }
    backup << content;
    backup.close();
    
    // Sort references in reverse order to avoid offset shifts
    std::vector<verible::TokenInfo> sorted_refs = file_refs;
    std::sort(sorted_refs.begin(), sorted_refs.end(),
              [&content](const verible::TokenInfo& a, const verible::TokenInfo& b) {
                int pos_a = std::distance(content.begin(),
                                         content.begin() + (a.text().data() - content.data()));
                int pos_b = std::distance(content.begin(),
                                         content.begin() + (b.text().data() - content.data()));
                return pos_a > pos_b; // Reverse order
              });
    
    // Apply replacements
    for (const auto& ref : sorted_refs) {
      int pos = std::distance(content.begin(),
                             content.begin() + (ref.text().data() - content.data()));
      content.replace(pos, old_name.size(), new_name);
    }
    
    // Write modified content
    std::ofstream output(filename);
    if (!output.is_open()) {
      return absl::InternalError(
          absl::StrCat("Failed to open file for writing: ", filename));
    }
    output << content;
    output.close();
    
    report.modified_files.push_back(filename);
  }
  
  report.summary = absl::StrCat(
      "Renamed '", old_name, "' to '", new_name, "': ",
      report.occurrences_renamed, " occurrences in ",
      report.files_modified, " file(s)");
  
  return report;
}

bool SymbolRenamer::IsInScope(const verilog::SymbolTableNode& node,
                               const verible::Symbol& scope) const {
  // Simplified scope checking: For now, return true if symbol_table exists
  // Full implementation would traverse the symbol table hierarchy
  // to verify the node is actually within the specified scope
  return symbol_table_ != nullptr;
}

}  // namespace tools
}  // namespace verilog

