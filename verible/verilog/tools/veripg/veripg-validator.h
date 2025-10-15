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

#ifndef VERIBLE_VERILOG_TOOLS_VERIPG_VERIPG_VALIDATOR_H_
#define VERIBLE_VERILOG_TOOLS_VERIPG_VERIPG_VALIDATOR_H_

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-checker.h"

namespace verilog {
namespace tools {

// Validation result for VeriPG
struct ValidationResult {
  bool passed = false;
  int errors_found = 0;
  int warnings_found = 0;
  std::vector<std::string> error_messages;
  std::vector<std::string> warning_messages;
  std::string summary;
};

// VeriPGValidator provides enhanced semantic validation for VeriPG workflows
class VeriPGValidator {
 public:
  // Construct with type checker for semantic analysis
  explicit VeriPGValidator(const verilog::analysis::TypeChecker* type_checker);

  // Perform full VeriPG validation
  ValidationResult Validate(const verilog::SymbolTable& symbol_table);

  // Validate type safety
  absl::Status ValidateTypes(const verilog::SymbolTable& symbol_table);

  // Validate naming conventions (VeriPG-specific)
  absl::Status ValidateNamingConventions(const verilog::SymbolTable& symbol_table);

  // Validate module structure
  absl::Status ValidateModuleStructure(const verilog::SymbolTable& symbol_table);

 private:
  const verilog::analysis::TypeChecker* type_checker_;
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_VERIPG_VERIPG_VALIDATOR_H_

