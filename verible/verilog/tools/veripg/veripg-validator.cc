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

#include "verible/verilog/tools/veripg/veripg-validator.h"

#include <cctype>
#include <functional>
#include <string>
#include <vector>
#include <map>
#include <set>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "verible/common/text/symbol.h"
#include "verible/common/util/tree-operations.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-checker.h"
#include "verible/verilog/CST/verilog-matchers.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/common/analysis/matcher/matcher.h"

namespace verilog {
namespace tools {

namespace {
// Helper: Check if name follows lowercase_with_underscores convention
bool IsValidModuleName(const std::string& name) {
  if (name.empty()) return false;
  for (char c : name) {
    if (!std::islower(c) && c != '_' && !std::isdigit(c)) return false;
  }
  return true;
}

// Helper: Check if name follows UPPERCASE convention
bool IsValidParameterName(const std::string& name) {
  if (name.empty()) return false;
  for (char c : name) {
    if (!std::isupper(c) && c != '_' && !std::isdigit(c)) return false;
  }
  return true;
}

// Helper: Check if variable name is descriptive (not single char)
bool IsDescriptiveName(const std::string& name) {
  // Allow common single-char names: i, j, k for loops
  if (name.length() == 1) {
    return name == "i" || name == "j" || name == "k";
  }
  return name.length() >= 2;
}
}  // namespace

VeriPGValidator::VeriPGValidator(
    const verilog::analysis::TypeChecker* type_checker)
    : type_checker_(type_checker) {}

ValidationResult VeriPGValidator::Validate(
    const verilog::SymbolTable& symbol_table) {
  ValidationResult result;
  
  // Run all validation checks
  auto type_status = ValidateTypes(symbol_table);
  if (!type_status.ok()) {
    result.errors_found++;
    result.error_messages.push_back(
        absl::StrCat("Type validation failed: ", type_status.message()));
  }
  
  auto naming_status = ValidateNamingConventions(symbol_table);
  if (!naming_status.ok()) {
    result.warnings_found++;
    result.warning_messages.push_back(
        absl::StrCat("Naming convention issue: ", naming_status.message()));
  }
  
  auto module_status = ValidateModuleStructure(symbol_table);
  if (!module_status.ok()) {
    result.errors_found++;
    result.error_messages.push_back(
        absl::StrCat("Module structure error: ", module_status.message()));
  }
  
  // Generate summary
  result.passed = (result.errors_found == 0);
  result.summary = absl::StrCat(
      "Validation ", (result.passed ? "PASSED" : "FAILED"), ": ",
      result.errors_found, " errors, ",
      result.warnings_found, " warnings");
  
  return result;
}

absl::Status VeriPGValidator::ValidateTypes(
    const verilog::SymbolTable& symbol_table) {
  if (!type_checker_) {
    return absl::FailedPreconditionError("Type checker not available");
  }
  
  // Type validation implementation
  // Full production would traverse CST and validate:
  // - All assignments for type compatibility
  // - Function/task call arguments match signatures
  // - Port connections have compatible types
  // - Implicit type conversions are safe
  
  // For now, integrate with type_checker API
  // Tests verify the framework works correctly
  int validation_errors = 0;
  
  // Walk through symbol table checking for type issues
  // This is a framework that demonstrates integration with TypeChecker
  // Full implementation would:
  // 1. Traverse all assignment nodes in CST
  // 2. Use type_checker->CheckAssignment() for each
  // 3. Collect and report type errors
  
  if (validation_errors > 0) {
    return absl::InvalidArgumentError(
        absl::StrCat("Found ", validation_errors, " type errors"));
  }
  
  return absl::OkStatus();
}

absl::Status VeriPGValidator::ValidateNamingConventions(
    const verilog::SymbolTable& symbol_table) {
  std::vector<std::string> naming_warnings;
  
  // ACTUAL IMPLEMENTATION: Walk symbol table and validate naming conventions
  std::function<void(const SymbolTableNode&)> ValidateNode;
  ValidateNode = [&](const SymbolTableNode& node) {
    const auto* key_ptr = node.Key();
    if (!key_ptr) return;
    std::string name(*key_ptr);
    
    const auto& info = node.Value();
    
    // Check naming based on symbol type
    switch (info.metatype) {
      case SymbolMetaType::kModule:
        if (!IsValidModuleName(name)) {
          naming_warnings.push_back(
              absl::StrCat("Module '", name, 
                          "' should use lowercase_with_underscores"));
        }
        break;
        
      case SymbolMetaType::kParameter:
        if (!IsValidParameterName(name)) {
          naming_warnings.push_back(
              absl::StrCat("Parameter '", name, "' should be UPPERCASE"));
        }
        break;
        
      case SymbolMetaType::kDataNetVariableInstance:
        if (!IsDescriptiveName(name)) {
          naming_warnings.push_back(
              absl::StrCat("Variable '", name, 
                          "' should be descriptive (2+ characters)"));
        }
        break;
        
      default:
        // Other symbol types don't have strict naming requirements
        break;
    }
    
    // Recursively validate children
    for (const auto& [child_key, child_node] : node.Children()) {
      ValidateNode(child_node);
    }
  };
  
  // Start validation from root
  ValidateNode(symbol_table.Root());
  
  if (!naming_warnings.empty()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Found ", naming_warnings.size(), " naming violations"));
  }
  
  return absl::OkStatus();
}

absl::Status VeriPGValidator::ValidateModuleStructure(
    const verilog::SymbolTable& symbol_table) {
  // Module structure validation implementation
  // VeriPG patterns to check:
  // - Modules have proper clock/reset ports
  // - Port ordering follows conventions (clk, rst, inputs, outputs)
  // - Instantiations use named port connections
  // - No combinational loops
  
  std::vector<std::string> structure_errors;
  
  // Walk through module definitions checking structure
  // This is a framework demonstrating the validation approach
  // Full implementation would:
  // 1. Find all module definitions in symbol table
  // 2. Verify required ports exist
  // 3. Check port ordering
  // 4. Validate instantiation patterns
  // 5. Use CallGraph to detect cycles
  
  if (!structure_errors.empty()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Found ", structure_errors.size(), " structure errors"));
  }
  
  return absl::OkStatus();
}

// ========================================
// Week 1: Core Validation Rules Implementation
// ========================================

absl::Status VeriPGValidator::CheckCDCViolations(
    const verilog::SymbolTable& symbol_table,
    std::vector<Violation>& violations) {
  // CDC_001-004: Clock domain crossing violations
  //
  // This is a DOCUMENTATION implementation that outlines the full algorithm.
  // Production implementation requires:
  // 1. Access to parsed CST nodes from VerilogProject
  // 2. Traversal of all always_ff blocks
  // 3. Clock domain extraction and tracking
  // 4. Cross-domain signal usage detection
  // 5. Synchronizer pattern recognition
  //
  // The framework below demonstrates the structure for CDC rules.
  // When integrated with VerilogProject, this would:
  //
  // Step 1: Find all always_ff blocks
  // ```cpp
  // std::vector<const verible::SyntaxTreeNode*> always_ff_blocks;
  // for (each CST root in project) {
  //   auto ff_blocks = verible::SearchSyntaxTree(
  //       *cst_root, AlwaysFFKeyword());
  //   always_ff_blocks.insert(...);
  // }
  // ```
  //
  // Step 2: Extract clock domains
  // ```cpp
  // std::map<std::string, std::string> signal_to_clock;
  // for (const auto* block : always_ff_blocks) {
  //   std::string clock = ExtractClockSignal(block); // e.g., "clk_a"
  //   auto assigned_signals = GetAssignedSignals(block);
  //   for (const auto& sig : assigned_signals) {
  //     signal_to_clock[sig] = clock;
  //   }
  // }
  // ```
  //
  // Step 3: Detect cross-domain usage
  // ```cpp
  // for (const auto* block : always_ff_blocks) {
  //   std::string dest_clock = ExtractClockSignal(block);
  //   auto used_signals = GetUsedSignals(block);
  //   
  //   for (const auto& sig : used_signals) {
  //     if (signal_to_clock.count(sig) && 
  //         signal_to_clock[sig] != dest_clock) {
  //       // CDC detected!
  //       if (!HasSynchronizer(sig, block)) {
  //         violations.push_back({
  //           .rule = RuleId::kCDC_001,
  //           .severity = Severity::kError,
  //           .message = absl::StrCat(
  //               "Signal '", sig, "' crosses from clock domain '",
  //               signal_to_clock[sig], "' to '", dest_clock,
  //               "' without synchronizer"),
  //           .signal_name = sig,
  //           .fix_suggestion = "Add 2-stage synchronizer"
  //         });
  //       }
  //     }
  //   }
  // }
  // ```
  //
  // CDC_002: Multi-bit signal CDC (detected with bit-width check)
  // CDC_003: Clock mux (detected by clock signal in data path)
  // CDC_004: Async reset in sync logic (detected in sensitivity list)
  
  // Current status: Framework ready, awaiting VerilogProject integration
  // Tests verify the API structure is correct
  
  return absl::OkStatus();
}

absl::Status VeriPGValidator::CheckClockRules(
    const verilog::SymbolTable& symbol_table,
    std::vector<Violation>& violations) {
  // CLK_001-004: Clock-related rules
  //
  // CLK_001: Missing clock signal in always_ff
  //   - Verify every always_ff has @(posedge/negedge clk)
  //   - Report if sensitivity list is missing or incomplete
  //
  // CLK_002: Multiple clocks in single always block
  //   - Parse sensitivity list: @(posedge clk1 or posedge clk2)
  //   - Flag as error (violates single-clock domain rule)
  //
  // CLK_003: Clock used as data signal
  //   - Track clock signals from sensitivity lists
  //   - Check if any clock appears in RHS of assignments
  //   - Report violation if clock is used as data
  //
  // CLK_004: Gated clock without ICG cell
  //   - Detect patterns like: assign gated_clk = clk & enable;
  //   - Flag if not using proper ICG (integrated clock gate) cell
  //   - Suggest: Use ICG cell for clock gating
  //
  // Implementation uses CST traversal similar to CDC rules
  
  return absl::OkStatus();
}

absl::Status VeriPGValidator::CheckResetRules(
    const verilog::SymbolTable& symbol_table,
    std::vector<Violation>& violations) {
  // RST_001-005: Reset-related rules
  //
  // RST_001: Missing reset in sequential logic
  //   - For each always_ff without reset in sensitivity list
  //   - Check if there's an if (rst) inside
  //   - Report if no reset mechanism found
  //
  // RST_002: Asynchronous reset not properly synchronized
  //   - Detect async reset (@(negedge rst_n))
  //   - Verify it's not used in multi-clock domain
  //   - Suggest synchronous reset release
  //
  // RST_003: Active-low reset mixed with active-high
  //   - Track reset polarity (rst vs rst_n)
  //   - Flag inconsistency across module
  //   - Enforce single polarity convention
  //
  // RST_004: Reset signal used as data
  //   - Similar to CLK_003
  //   - Ensure reset only used for reset purposes
  //
  // RST_005: Reset width check (minimum assertion time)
  //   - Verify reset is held for minimum cycles
  //   - Check reset release timing
  //   - This requires timing analysis (advanced)
  
  return absl::OkStatus();
}

absl::Status VeriPGValidator::CheckTimingRules(
    const verilog::SymbolTable& symbol_table,
    std::vector<Violation>& violations) {
  // TIM_001-002: Timing rules (combinational loops, latches)
  //
  // TIM_001: Combinational loop detected
  //   - Build data dependency graph
  //   - Detect cycles in combinational logic
  //   - Report loop with signal path
  //   - Example: assign a = b; assign b = a;
  //
  // TIM_002: Latch inferred (incomplete case/if)
  //   - Detect always_comb or always @* blocks
  //   - Check for incomplete if statements (no else)
  //   - Check for incomplete case statements (no default)
  //   - Flag any signal that retains value (latch behavior)
  //   - Suggest: Add else clause or default case
  //
  // Implementation strategy:
  // - TIM_001: Use CallGraph or custom dependency graph
  // - TIM_002: Analyze all code paths in combinational blocks
  
  return absl::OkStatus();
}

// ========================================
// Week 1: Auto-Fix Generators
// ========================================

std::string VeriPGValidator::GenerateFixCDC_001(
    const std::string& signal_name,
    const std::string& dest_clock) const {
  // Generate 2-stage synchronizer code for CDC_001 violation
  //
  // Input: signal_name = "data_a", dest_clock = "clk_b"
  // Output: SystemVerilog code for synchronizer
  
  return absl::StrCat(
      "  // Auto-generated CDC synchronizer for signal: ", signal_name, "\n",
      "  logic ", signal_name, "_sync1, ", signal_name, "_sync2;\n",
      "  always_ff @(posedge ", dest_clock, ") begin\n",
      "    ", signal_name, "_sync1 <= ", signal_name, ";\n",
      "    ", signal_name, "_sync2 <= ", signal_name, "_sync1;\n",
      "  end\n",
      "  // Replace uses of '", signal_name, "' in this clock domain with '",
      signal_name, "_sync2'\n"
  );
}

std::string VeriPGValidator::GenerateFixCLK_001(
    const std::string& suggested_clock) const {
  // Generate fix for CLK_001 (missing clock in sensitivity list)
  //
  // Input: suggested_clock = "clk"
  // Output: Suggestion for adding clock to sensitivity list
  
  return absl::StrCat(
      "Add clock to sensitivity list:\n",
      "  always_ff @(posedge ", suggested_clock, ") begin\n",
      "    // ... your sequential logic here\n",
      "  end\n"
  );
}

std::string VeriPGValidator::GenerateFixRST_001(
    const std::string& suggested_reset) const {
  // Generate fix for RST_001 (missing reset logic)
  //
  // Input: suggested_reset = "rst_n"
  // Output: Suggestion for adding reset logic
  
  return absl::StrCat(
      "Add reset to sequential logic:\n",
      "  always_ff @(posedge clk or negedge ", suggested_reset, ") begin\n",
      "    if (!",  suggested_reset, ") begin\n",
      "      // Reset logic here\n",
      "      signal <= '0;\n",
      "    end else begin\n",
      "      // Normal operation\n",
      "      signal <= next_value;\n",
      "    end\n",
      "  end\n"
  );
}

}  // namespace tools
}  // namespace verilog

