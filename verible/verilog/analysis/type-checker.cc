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

#include "verible/verilog/analysis/type-checker.h"

#include <string>

#include "absl/strings/str_cat.h"

namespace verilog {
namespace analysis {

TypeChecker::TypeChecker(const SymbolTable* symbol_table,
                         const TypeInference* type_inference)
    : symbol_table_(symbol_table), type_inference_(type_inference) {}

absl::Status TypeChecker::CheckAssignment(const verible::Symbol& lhs,
                                          const verible::Symbol& rhs) {
  // Infer types of both sides
  const Type* lhs_type = type_inference_->InferType(lhs);
  const Type* rhs_type = type_inference_->InferType(rhs);
  
  if (!lhs_type || !rhs_type) {
    AddError("Cannot infer types for assignment");
    return absl::InvalidArgumentError("Type inference failed");
  }
  
  // Use TypeCompatibilityChecker for comprehensive checking
  auto compat_result = TypeCompatibilityChecker::CheckAssignment(*lhs_type, *rhs_type);
  
  // Handle compatibility result based on level
  if (compat_result.IsError()) {
    // Incompatible types (e.g., string to int)
    std::string error_msg = absl::StrCat(
        "Type error in assignment: ", compat_result.message,
        " (", lhs_type->ToString(), " = ", rhs_type->ToString(), ")");
    AddError(error_msg);
    return absl::InvalidArgumentError(error_msg);
  }
  
  if (compat_result.IsWarning()) {
    // Potentially problematic assignment
    // Check if warnings are enabled for this specific issue
    bool should_warn = false;
    
    // Check if it's a narrowing warning
    if (options_.warn_narrowing && 
        compat_result.message.find("Truncation") != std::string::npos) {
      should_warn = true;
    }
    
    // Check if it's a sign mismatch warning
    if (options_.warn_sign_mismatch &&
        (compat_result.message.find("signed") != std::string::npos ||
         compat_result.message.find("unsigned") != std::string::npos)) {
      should_warn = true;
    }
    
    // Check for state mismatch (X/Z loss)
    if (compat_result.message.find("X/Z") != std::string::npos ||
        compat_result.message.find("state") != std::string::npos) {
      should_warn = true;
    }
    
    // Check for precision loss (real to integral)
    if (compat_result.message.find("precision") != std::string::npos) {
      should_warn = true;
    }
    
    if (should_warn) {
      std::string warn_msg = absl::StrCat(
          "Type warning in assignment: ", compat_result.message,
          " (", lhs_type->ToString(), " = ", rhs_type->ToString(), ")");
      
      // If warnings_as_errors is enabled, treat as error
      if (options_.warnings_as_errors) {
        AddError(warn_msg);
        return absl::InvalidArgumentError(warn_msg);
      } else {
        AddWarning(warn_msg);
      }
    }
  }
  
  // kExact or kSafe - assignment is OK
  return absl::OkStatus();
}

absl::Status TypeChecker::CheckBinaryOperator(const verible::Symbol& op,
                                               const verible::Symbol& lhs,
                                               const verible::Symbol& rhs) {
  // Infer types of operands
  const Type* lhs_type = type_inference_->InferType(lhs);
  const Type* rhs_type = type_inference_->InferType(rhs);
  
  if (!lhs_type || !rhs_type) {
    AddError("Cannot infer operand types");
    return absl::InvalidArgumentError("Type inference failed");
  }
  
  // Determine operator type (simplified - would need actual operator token)
  // For now, assume arithmetic by default
  TypeCompatibilityChecker::BinaryOpType op_type = 
      TypeCompatibilityChecker::BinaryOpType::kArithmetic;
  
  // Check operator compatibility using TypeCompatibilityChecker
  auto compat_result = TypeCompatibilityChecker::CheckBinaryOp(
      *lhs_type, *rhs_type, op_type);
  
  if (compat_result.IsError()) {
    std::string error_msg = absl::StrCat(
        "Type error in binary operation: ", compat_result.message,
        " (", lhs_type->ToString(), " op ", rhs_type->ToString(), ")");
    AddError(error_msg);
    return absl::InvalidArgumentError(error_msg);
  }
  
  if (compat_result.IsWarning()) {
    // Check if we should warn based on options
    if (options_.warn_sign_mismatch || options_.warn_narrowing) {
      std::string warn_msg = absl::StrCat(
          "Type warning in binary operation: ", compat_result.message,
          " (", lhs_type->ToString(), " op ", rhs_type->ToString(), ")");
      
      if (options_.warnings_as_errors) {
        AddError(warn_msg);
        return absl::InvalidArgumentError(warn_msg);
      } else {
        AddWarning(warn_msg);
      }
    }
  }
  
  return absl::OkStatus();
}

absl::Status TypeChecker::CheckUnaryOperator(const verible::Symbol& op,
                                              const verible::Symbol& operand) {
  const Type* operand_type = type_inference_->InferType(operand);
  
  if (!operand_type) {
    AddError("Cannot infer operand type");
    return absl::InvalidArgumentError("Type inference failed");
  }
  
  // Simplified: check if operand is numeric
  if (!operand_type->IsNumeric()) {
    std::string error_msg = absl::StrCat(
        "Operator requires numeric operand, got ", operand_type->ToString());
    AddError(error_msg);
    return absl::InvalidArgumentError(error_msg);
  }
  
  return absl::OkStatus();
}

absl::Status TypeChecker::CheckFunctionCall(const verible::Symbol& call) {
  // Simplified implementation
  // Full version would extract function name, look up signature,
  // check each argument type against parameter types
  
  AddInfo("Function call type checking not yet fully implemented");
  return absl::OkStatus();
}

absl::Status TypeChecker::CheckCast(const Type& target_type,
                                    const verible::Symbol& expr) {
  const Type* source_type = type_inference_->InferType(expr);
  
  if (!source_type) {
    AddError("Cannot infer source type for cast");
    return absl::InvalidArgumentError("Type inference failed");
  }
  
  if (!IsCastValid(target_type, *source_type)) {
    std::string error_msg = absl::StrCat(
        "Invalid cast from ", source_type->ToString(),
        " to ", target_type.ToString());
    AddError(error_msg);
    return absl::InvalidArgumentError(error_msg);
  }
  
  return absl::OkStatus();
}

size_t TypeChecker::GetErrorCount() const {
  size_t count = 0;
  for (const auto& issue : issues_) {
    if (issue.severity == TypeCheckSeverity::kError) {
      count++;
    }
  }
  
  // If warnings are treated as errors, count them too
  if (options_.warnings_as_errors) {
    for (const auto& issue : issues_) {
      if (issue.severity == TypeCheckSeverity::kWarning) {
        count++;
      }
    }
  }
  
  return count;
}

size_t TypeChecker::GetWarningCount() const {
  size_t count = 0;
  for (const auto& issue : issues_) {
    if (issue.severity == TypeCheckSeverity::kWarning) {
      count++;
    }
  }
  return count;
}

bool TypeChecker::IsAssignmentCompatible(const Type& lhs_type,
                                         const Type& rhs_type) {
  // In strict mode, types must match exactly
  if (options_.strict_mode) {
    return lhs_type == rhs_type;
  }
  
  // Otherwise, use the Type's IsAssignableFrom method
  return lhs_type.IsAssignableFrom(rhs_type);
}

bool TypeChecker::IsOperatorCompatible(const Type& lhs_type,
                                       const Type& rhs_type,
                                       int op_token) {
  // Simplified: both operands should be numeric for most operators
  // Full implementation would check operator-specific requirements
  return lhs_type.IsNumeric() && rhs_type.IsNumeric();
}

bool TypeChecker::IsCastValid(const Type& target_type,
                              const Type& source_type) {
  // Most casts between numeric types are valid (though may lose precision)
  if (target_type.IsNumeric() && source_type.IsNumeric()) {
    return true;
  }
  
  // String casts are not allowed
  if (target_type.IsString() || source_type.IsString()) {
    return false;
  }
  
  // User-defined types must match exactly
  if (target_type.IsUserDefined() && source_type.IsUserDefined()) {
    return target_type.user_type_name == source_type.user_type_name;
  }
  
  return false;
}

void TypeChecker::AddError(std::string_view message, std::string_view file,
                           int line, int col) {
  issues_.emplace_back(TypeCheckSeverity::kError, message, file, line, col);
}

void TypeChecker::AddWarning(std::string_view message, std::string_view file,
                             int line, int col) {
  issues_.emplace_back(TypeCheckSeverity::kWarning, message, file, line, col);
}

void TypeChecker::AddInfo(std::string_view message, std::string_view file,
                          int line, int col) {
  issues_.emplace_back(TypeCheckSeverity::kInfo, message, file, line, col);
}

std::string TypeChecker::FormatTypeError(const Type& expected,
                                         const Type& actual) {
  return absl::StrCat("Type mismatch: expected ", expected.ToString(),
                      ", got ", actual.ToString());
}

std::string TypeChecker::FormatNarrowingWarning(const Type& from,
                                                const Type& to) {
  return absl::StrCat("Narrowing conversion from ", from.ToString(),
                      " (", from.GetWidth(), " bits) to ", to.ToString(),
                      " (", to.GetWidth(), " bits)");
}

std::string TypeChecker::FormatSignMismatchWarning(const Type& lhs,
                                                   const Type& rhs) {
  return absl::StrCat("Sign mismatch: ",
                      lhs.is_signed ? "signed" : "unsigned", " ",
                      lhs.ToString(), " vs ",
                      rhs.is_signed ? "signed" : "unsigned", " ",
                      rhs.ToString());
}

// Week 2: Function & Task Validation Implementations

absl::Status TypeChecker::ValidateFunctionCall(
    const verible::Symbol& call_site,
    const std::string& function_name,
    const std::vector<const verible::Symbol*>& arguments) {
  // Simplified: Look up function in symbol table and check arguments
  // Full implementation would traverse symbol table to find function declaration
  
  // For now, just validate argument types are inferrable
  for (size_t i = 0; i < arguments.size(); ++i) {
    if (arguments[i]) {
      const Type* arg_type = type_inference_->InferType(*arguments[i]);
      if (!arg_type || arg_type->IsUnknown()) {
        return absl::InvalidArgumentError(
            absl::StrCat("Cannot infer type for argument ", i, 
                        " in call to function '", function_name, "'"));
      }
    }
  }
  
  return absl::OkStatus();
}

absl::Status TypeChecker::ValidateTaskCall(
    const verible::Symbol& call_site,
    const std::string& task_name,
    const std::vector<const verible::Symbol*>& arguments) {
  // Similar to function validation, but tasks don't have return types
  
  for (size_t i = 0; i < arguments.size(); ++i) {
    if (arguments[i]) {
      const Type* arg_type = type_inference_->InferType(*arguments[i]);
      if (!arg_type || arg_type->IsUnknown()) {
        return absl::InvalidArgumentError(
            absl::StrCat("Cannot infer type for argument ", i,
                        " in call to task '", task_name, "'"));
      }
    }
  }
  
  return absl::OkStatus();
}

absl::Status TypeChecker::CheckArgumentCount(const std::string& callable_name,
                                              size_t expected_count,
                                              size_t actual_count) const {
  if (expected_count != actual_count) {
    return absl::InvalidArgumentError(
        absl::StrCat("Argument count mismatch in call to '", callable_name,
                    "': expected ", expected_count, " arguments, got ",
                    actual_count));
  }
  return absl::OkStatus();
}

absl::Status TypeChecker::CheckArgumentType(const std::string& callable_name,
                                             size_t arg_index,
                                             const Type* expected_type,
                                             const Type* actual_type) const {
  if (!expected_type || !actual_type) {
    return absl::UnknownError(
        absl::StrCat("Cannot determine types for argument ", arg_index,
                    " in call to '", callable_name, "'"));
  }
  
  if (!expected_type->IsAssignableFrom(*actual_type)) {
    return absl::InvalidArgumentError(
        absl::StrCat("Type mismatch for argument ", arg_index,
                    " in call to '", callable_name, "': expected ",
                    expected_type->ToString(), ", got ",
                    actual_type->ToString()));
  }
  
  return absl::OkStatus();
}

absl::Status TypeChecker::CheckReturnType(const std::string& function_name,
                                          const Type* expected_return,
                                          const Type* actual_return) const {
  if (!expected_return || !actual_return) {
    return absl::UnknownError(
        absl::StrCat("Cannot determine return type for function '",
                    function_name, "'"));
  }
  
  if (!expected_return->IsAssignableFrom(*actual_return)) {
    return absl::InvalidArgumentError(
        absl::StrCat("Return type mismatch for function '", function_name,
                    "': expected ", expected_return->ToString(), ", got ",
                    actual_return->ToString()));
  }
  
  return absl::OkStatus();
}

absl::Status TypeChecker::CheckParameterDirection(
    const std::string& callable_name,
    size_t arg_index,
    const std::string& expected_direction,
    const verible::Symbol& argument) const {
  // Simplified: Check if argument can be used with given direction
  // Full implementation would analyze if argument is lvalue (for output/inout)
  
  // For output/inout, argument should be an lvalue (variable, port, etc)
  if (expected_direction == "output" || expected_direction == "inout") {
    // Simplified check: if we can't infer type, it might not be an lvalue
    const Type* arg_type = type_inference_->InferType(argument);
    if (!arg_type || arg_type->IsUnknown()) {
      return absl::InvalidArgumentError(
          absl::StrCat("Argument ", arg_index, " in call to '", callable_name,
                      "' must be an lvalue for ", expected_direction,
                      " parameter"));
    }
  }
  
  return absl::OkStatus();
}

}  // namespace analysis
}  // namespace verilog

