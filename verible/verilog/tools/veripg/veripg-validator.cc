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

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "verible/common/text/symbol.h"
#include "verible/common/util/tree-operations.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-checker.h"

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
  // CDC_001: Clock domain crossing without synchronizer
  // 
  // Algorithm:
  // 1. Find all always_ff blocks and their clock domains
  // 2. For each signal assigned in one clock domain:
  //    - Find uses of that signal in other clock domains
  //    - Check if there's a 2-stage synchronizer pattern
  //    - If not, report CDC_001 violation
  
  // TODO: Full implementation requires:
  // - CST traversal to find always_ff blocks
  // - Clock domain extraction from sensitivity lists
  // - Data flow analysis to track signal uses across domains
  // - Synchronizer pattern detection
  
  // Framework: Return OK for now, actual detection will be added
  // based on symbol table analysis and CST traversal
  
  return absl::OkStatus();
}

absl::Status VeriPGValidator::CheckClockRules(
    const verilog::SymbolTable& symbol_table,
    std::vector<Violation>& violations) {
  // CLK_001-004: Clock-related rules
  return absl::OkStatus();
}

absl::Status VeriPGValidator::CheckResetRules(
    const verilog::SymbolTable& symbol_table,
    std::vector<Violation>& violations) {
  // RST_001-005: Reset-related rules
  return absl::OkStatus();
}

absl::Status VeriPGValidator::CheckTimingRules(
    const verilog::SymbolTable& symbol_table,
    std::vector<Violation>& violations) {
  // TIM_001-002: Timing rules (combinational loops, latches)
  return absl::OkStatus();
}

}  // namespace tools
}  // namespace verilog

