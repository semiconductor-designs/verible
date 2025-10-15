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

#ifndef VERIBLE_VERILOG_TOOLS_RENAME_SYMBOL_RENAMER_H_
#define VERIBLE_VERILOG_TOOLS_RENAME_SYMBOL_RENAMER_H_

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "verible/common/text/token-info.h"
#include "verible/common/text/symbol.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-inference.h"

namespace verilog {
namespace tools {

// Report generated after a rename operation
struct RenameReport {
  int files_modified = 0;
  int occurrences_renamed = 0;
  std::vector<std::string> modified_files;
  std::string summary;
};

// SymbolRenamer provides semantic-aware symbol renaming with scope handling
class SymbolRenamer {
 public:
  // Construct a SymbolRenamer with required semantic analysis components
  explicit SymbolRenamer(const verilog::SymbolTable* symbol_table,
                         const verilog::analysis::TypeInference* type_inference);

  // Find all references to a symbol within a given scope
  // Returns TokenInfo positions for each reference
  std::vector<verible::TokenInfo> FindReferences(
      const std::string& symbol_name,
      const verible::Symbol& scope);

  // Validate that renaming old_name to new_name is safe
  // Checks for naming conflicts and shadowing issues
  absl::Status ValidateRename(const std::string& old_name,
                               const std::string& new_name,
                               const verible::Symbol& scope);

  // Perform rename operation with scope awareness
  // If dry_run is true, validation is performed but no changes are made
  // Returns a report of the rename operation
  absl::StatusOr<RenameReport> Rename(const std::string& old_name,
                                      const std::string& new_name,
                                      const verible::Symbol& scope,
                                      bool dry_run = false);

 private:
  const verilog::SymbolTable* symbol_table_;
  const verilog::analysis::TypeInference* type_inference_;

  // Helper: Check if a symbol table node is within the given scope
  bool IsInScope(const verilog::SymbolTableNode& node,
                 const verible::Symbol& scope) const;
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_RENAME_SYMBOL_RENAMER_H_

