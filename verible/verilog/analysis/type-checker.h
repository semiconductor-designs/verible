// Copyright 2025 The Verible Authors.
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

#ifndef VERIBLE_VERILOG_ANALYSIS_TYPE_CHECKER_H_
#define VERIBLE_VERILOG_ANALYSIS_TYPE_CHECKER_H_

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "verible/common/text/symbol.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-inference.h"
#include "verible/verilog/analysis/type-representation.h"

namespace verilog {
namespace analysis {

// Severity level for type check issues.
enum class TypeCheckSeverity {
  kError,    // Type error - code is invalid
  kWarning,  // Type warning - potentially problematic
  kInfo,     // Type info - informational only
};

// Represents a type checking error or warning.
struct TypeCheckIssue {
  TypeCheckSeverity severity;
  std::string message;
  std::string file_path;
  int line_number = 0;
  int column_number = 0;
  
  // Optional: suggested fix
  std::string suggestion;
  
  TypeCheckIssue(TypeCheckSeverity severity, std::string_view message,
                 std::string_view file_path = "", int line = 0, int col = 0)
      : severity(severity), message(message), file_path(file_path),
        line_number(line), column_number(col) {}
};

// TypeChecker validates type compatibility in SystemVerilog code.
//
// It uses TypeInference to determine expression types and validates:
// - Assignment type compatibility
// - Operator type compatibility
// - Function/task argument types
// - Return type checking
// - Cast validity
//
// Usage:
//   TypeChecker checker(&symbol_table, &type_inference);
//   
//   // Configure options
//   TypeChecker::Options opts;
//   opts.strict_mode = true;
//   checker.SetOptions(opts);
//   
//   // Check assignments
//   absl::Status status = checker.CheckAssignment(lhs, rhs);
//   
//   // Get all issues
//   const auto& issues = checker.GetIssues();
//   for (const auto& issue : issues) {
//     std::cout << issue.file_path << ":" << issue.line_number 
//               << ": " << issue.message << "\n";
//   }
class TypeChecker {
 public:
  // Configuration options for type checking.
  struct Options {
    // If true, enforce strict type checking (no implicit conversions).
    bool strict_mode = false;
    
    // If true, warn about implicit type casts.
    bool warn_implicit_casts = true;
    
    // If true, warn about narrowing conversions (wider to narrower).
    bool warn_narrowing = true;
    
    // If true, warn about signed/unsigned mismatches.
    bool warn_sign_mismatch = true;
    
    // If true, treat warnings as errors.
    bool warnings_as_errors = false;
  };
  
  // Constructor takes symbol table and type inference engine.
  TypeChecker(const SymbolTable* symbol_table,
              const TypeInference* type_inference);
  
  // Check type compatibility of an assignment.
  // Returns OK if types are compatible, error otherwise.
  absl::Status CheckAssignment(const verible::Symbol& lhs,
                                const verible::Symbol& rhs);
  
  // Check type compatibility of a binary operator.
  absl::Status CheckBinaryOperator(const verible::Symbol& op,
                                    const verible::Symbol& lhs,
                                    const verible::Symbol& rhs);
  
  // Check type compatibility of a unary operator.
  absl::Status CheckUnaryOperator(const verible::Symbol& op,
                                   const verible::Symbol& operand);
  
  // Check function call argument types.
  absl::Status CheckFunctionCall(const verible::Symbol& call);
  
  // Check type cast validity.
  absl::Status CheckCast(const Type& target_type,
                         const verible::Symbol& expr);
  
  // Get all issues found during checking.
  const std::vector<TypeCheckIssue>& GetIssues() const {
    return issues_;
  }
  
  // Get count of errors (severity = kError).
  size_t GetErrorCount() const;
  
  // Get count of warnings (severity = kWarning).
  size_t GetWarningCount() const;
  
  // Clear all collected issues.
  void ClearIssues() { issues_.clear(); }
  
  // Check if there are any errors.
  bool HasErrors() const { return GetErrorCount() > 0; }
  
  // Set checking options.
  void SetOptions(const Options& options) { options_ = options; }
  
  // Get current options.
  const Options& GetOptions() const { return options_; }
  
  // Week 2: Function & Task Validation APIs
  
  // Validates function/task call with detailed argument checking
  absl::Status ValidateFunctionCall(const verible::Symbol& call_site,
                                     const std::string& function_name,
                                     const std::vector<const verible::Symbol*>& arguments);
  
  // Validates task call
  absl::Status ValidateTaskCall(const verible::Symbol& call_site,
                                 const std::string& task_name,
                                 const std::vector<const verible::Symbol*>& arguments);
  
  // Check argument count matches expected count
  absl::Status CheckArgumentCount(const std::string& callable_name,
                                   size_t expected_count,
                                   size_t actual_count) const;
  
  // Check argument type compatibility
  absl::Status CheckArgumentType(const std::string& callable_name,
                                  size_t arg_index,
                                  const Type* expected_type,
                                  const Type* actual_type) const;
  
  // Check return type compatibility
  absl::Status CheckReturnType(const std::string& function_name,
                                const Type* expected_return,
                                const Type* actual_return) const;
  
  // Check parameter direction (input/output/inout)
  absl::Status CheckParameterDirection(const std::string& callable_name,
                                        size_t arg_index,
                                        const std::string& expected_direction,
                                        const verible::Symbol& argument) const;
  
 private:
  const SymbolTable* symbol_table_;
  const TypeInference* type_inference_;
  std::vector<TypeCheckIssue> issues_;
  Options options_;
  
  // Helper methods for type checking.
  bool IsAssignmentCompatible(const Type& lhs_type, const Type& rhs_type);
  bool IsOperatorCompatible(const Type& lhs_type, const Type& rhs_type,
                            int op_token);
  bool IsCastValid(const Type& target_type, const Type& source_type);
  
  // Error reporting helpers.
  void AddError(std::string_view message, std::string_view file = "",
                int line = 0, int col = 0);
  void AddWarning(std::string_view message, std::string_view file = "",
                  int line = 0, int col = 0);
  void AddInfo(std::string_view message, std::string_view file = "",
               int line = 0, int col = 0);
  
  // Generate error messages.
  std::string FormatTypeError(const Type& expected, const Type& actual);
  std::string FormatNarrowingWarning(const Type& from, const Type& to);
  std::string FormatSignMismatchWarning(const Type& lhs, const Type& rhs);
};

}  // namespace analysis
}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_TYPE_CHECKER_H_

