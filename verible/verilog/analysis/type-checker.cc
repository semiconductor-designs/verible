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
  
  // Check if assignment is valid
  if (!IsAssignmentCompatible(*lhs_type, *rhs_type)) {
    std::string error_msg = FormatTypeError(*lhs_type, *rhs_type);
    AddError(error_msg);
    return absl::InvalidArgumentError(error_msg);
  }
  
  // Check for warnings
  if (options_.warn_narrowing && 
      lhs_type->GetWidth() < rhs_type->GetWidth()) {
    AddWarning(FormatNarrowingWarning(*rhs_type, *lhs_type));
  }
  
  if (options_.warn_sign_mismatch &&
      lhs_type->is_signed != rhs_type->is_signed) {
    AddWarning(FormatSignMismatchWarning(*lhs_type, *rhs_type));
  }
  
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
  
  // Check operator compatibility
  // For now, simplified: just check if both are numeric for arithmetic ops
  // Full implementation would check specific operator requirements
  if (!lhs_type->IsNumeric() || !rhs_type->IsNumeric()) {
    std::string error_msg = absl::StrCat(
        "Operator requires numeric operands, got ",
        lhs_type->ToString(), " and ", rhs_type->ToString());
    AddError(error_msg);
    return absl::InvalidArgumentError(error_msg);
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

}  // namespace analysis
}  // namespace verilog

