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

// Rule severity levels
enum class Severity {
  kError,
  kWarning,
  kInfo
};

// Validation rule IDs
enum class RuleId {
  // CDC rules
  kCDC_001,  // CDC without synchronizer
  kCDC_002,  // Multi-bit signal crossing clock domains
  kCDC_003,  // Clock mux without glitch protection
  kCDC_004,  // Asynchronous reset in synchronous logic
  
  // Clock rules
  kCLK_001,  // Missing clock signal in always_ff
  kCLK_002,  // Multiple clocks in single always block
  kCLK_003,  // Clock used as data signal
  kCLK_004,  // Gated clock without ICG cell
  
  // Reset rules
  kRST_001,  // Missing reset in sequential logic
  kRST_002,  // Asynchronous reset not properly synchronized
  kRST_003,  // Active-low reset mixed with active-high
  kRST_004,  // Reset signal used as data
  kRST_005,  // Reset width check
  
  // Timing rules
  kTIM_001,  // Combinational loop detected
  kTIM_002   // Latch inferred
};

// Single violation record
struct Violation {
  RuleId rule;
  Severity severity;
  std::string message;
  std::string signal_name;
  std::string source_location;  // File:line:col
  std::string fix_suggestion;
};

// Validation result for VeriPG
struct ValidationResult {
  bool passed = false;
  int errors_found = 0;
  int warnings_found = 0;
  std::vector<std::string> error_messages;
  std::vector<std::string> warning_messages;
  std::vector<Violation> violations;
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

  // Week 1: Core Validation Rules (CDC/Clock/Reset)
  
  // Check CDC violations (CDC_001-004)
  absl::Status CheckCDCViolations(const verilog::SymbolTable& symbol_table,
                                  std::vector<Violation>& violations);
  
  // Check clock rules (CLK_001-004)
  absl::Status CheckClockRules(const verilog::SymbolTable& symbol_table,
                               std::vector<Violation>& violations);
  
  // Check reset rules (RST_001-005)
  absl::Status CheckResetRules(const verilog::SymbolTable& symbol_table,
                               std::vector<Violation>& violations);
  
  // Check timing rules (TIM_001-002)
  absl::Status CheckTimingRules(const verilog::SymbolTable& symbol_table,
                                std::vector<Violation>& violations);

 private:
  const verilog::analysis::TypeChecker* type_checker_;
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_VERIPG_VERIPG_VALIDATOR_H_

