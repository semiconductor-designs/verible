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

// Forward declaration
class VerilogProject;

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
  kTIM_002,  // Latch inferred
  
  // Week 2: Naming Convention rules
  kNAM_001,  // Module names must be lowercase_with_underscores
  kNAM_002,  // Signal names must be descriptive (>= 3 chars)
  kNAM_003,  // Parameter names must be UPPERCASE
  kNAM_004,  // Clock signals must start with "clk_"
  kNAM_005,  // Reset signals must start with "rst_" or "rstn_"
  kNAM_006,  // Active-low signals must end with "_n"
  kNAM_007,  // No reserved keywords as identifiers
  
  // Week 2: Signal Width rules
  kWID_001,  // Signal width mismatch in assignment
  kWID_002,  // Implicit width conversion (lossy)
  kWID_003,  // Concatenation width mismatch
  kWID_004,  // Parameter width inconsistent with usage
  kWID_005,  // Port width mismatch in instantiation
  
  // Week 3: Power Intent rules
  kPWR_001,  // Missing power domain annotation
  kPWR_002,  // Level shifter required at domain boundary
  kPWR_003,  // Isolation cell required for power-down domain
  kPWR_004,  // Retention register without retention annotation
  kPWR_005,  // Always-on signal crossing to power-gated domain
  
  // Week 3: Structure rules
  kSTR_001,  // Module has no ports (should be testbench)
  kSTR_002,  // Module exceeds complexity threshold (50+ statements)
  kSTR_003,  // Deep hierarchy (>5 levels of instantiation)
  kSTR_004,  // Missing module header comment
  kSTR_005,  // Port ordering (clk, rst, inputs, outputs)
  kSTR_006,  // Instantiation without named ports
  kSTR_007,  // Generate block without label
  kSTR_008   // Case statement without default clause
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
  // Note: Requires VerilogProject for CST access
  absl::Status CheckCDCViolations(const verilog::SymbolTable& symbol_table,
                                  std::vector<Violation>& violations,
                                  const verilog::VerilogProject* project = nullptr);
  
  // Check clock rules (CLK_001-004)
  // Note: Requires VerilogProject for CST access
  absl::Status CheckClockRules(const verilog::SymbolTable& symbol_table,
                               std::vector<Violation>& violations,
                               const verilog::VerilogProject* project = nullptr);
  
  // Check reset rules (RST_001-005)
  // Note: Requires VerilogProject for CST access
  absl::Status CheckResetRules(const verilog::SymbolTable& symbol_table,
                               std::vector<Violation>& violations,
                               const verilog::VerilogProject* project = nullptr);
  
  // Check timing rules (TIM_001-002)
  // Note: Requires VerilogProject for CST access
  absl::Status CheckTimingRules(const verilog::SymbolTable& symbol_table,
                                std::vector<Violation>& violations,
                                const verilog::VerilogProject* project = nullptr);

  // Week 1: Auto-fix generators (3 generators for CDC_001, CLK_001, RST_001)
  
  // Generate fix for CDC_001 (add 2-stage synchronizer)
  std::string GenerateFixCDC_001(const std::string& signal_name,
                                 const std::string& dest_clock) const;
  
  // Generate fix for CLK_001 (add missing clock in sensitivity list)
  std::string GenerateFixCLK_001(const std::string& suggested_clock) const;
  
  // Generate fix for RST_001 (add missing reset logic)
  std::string GenerateFixRST_001(const std::string& suggested_reset) const;

  // Week 2: Naming & Width Validation
  
  // Check naming convention violations (NAM_001-007)
  absl::Status CheckNamingViolations(const verilog::SymbolTable& symbol_table,
                                     std::vector<Violation>& violations,
                                     const verilog::VerilogProject* project = nullptr);
  
  // Check signal width violations (WID_001-005)
  absl::Status CheckWidthViolations(const verilog::SymbolTable& symbol_table,
                                    std::vector<Violation>& violations);
  
  // Week 2: Auto-fix generators (2 generators for NAM_001, WID_001)
  
  // Generate fix for NAM_001 (convert to lowercase_with_underscores)
  std::string GenerateFixNAM_001(const std::string& current_name) const;
  
  // Generate fix for WID_001 (add explicit width cast)
  std::string GenerateFixWID_001(int lhs_width, int rhs_width,
                                 const std::string& signal_name) const;

  // Week 3: Power Intent & Structure Validation
  
  // Check power intent violations (PWR_001-005)
  absl::Status CheckPowerViolations(const verilog::SymbolTable& symbol_table,
                                    std::vector<Violation>& violations);
  
  // Check structural violations (STR_001-008)
  absl::Status CheckStructureViolations(const verilog::SymbolTable& symbol_table,
                                        std::vector<Violation>& violations);
  
  // Week 3: Auto-fix generators (2 generators for STR_005, STR_006)
  
  // Generate fix for STR_005 (reorder ports to clk, rst, inputs, outputs)
  std::string GenerateFixSTR_005(const std::vector<std::string>& current_order) const;
  
  // Generate fix for STR_006 (convert positional to named ports)
  std::string GenerateFixSTR_006(const std::string& instance_name,
                                 const std::vector<std::string>& port_names) const;

 private:
  const verilog::analysis::TypeChecker* type_checker_;
  
  // Helper methods for CDC detection
  std::string ExtractClockFromBlock(const verible::SyntaxTreeNode* block);
  std::vector<std::string> GetAssignedSignalsInBlock(const verible::SyntaxTreeNode* block);
  std::vector<std::string> GetUsedSignalsInBlock(const verible::SyntaxTreeNode* block);
  bool HasSynchronizerPattern(const std::string& signal, const verible::SyntaxTreeNode* block);
  bool IsMultiBitSignal(const std::string& signal, const verilog::SymbolTable& symbol_table);
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_VERIPG_VERIPG_VALIDATOR_H_

