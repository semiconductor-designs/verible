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

#include "verible/verilog/analysis/type-compatibility-rules.h"

#include <algorithm>
#include <sstream>

namespace verilog {
namespace analysis {

std::string CompatibilityResult::LevelToString() const {
  switch (level) {
    case CompatibilityLevel::kExact:
      return "Exact";
    case CompatibilityLevel::kSafe:
      return "Safe";
    case CompatibilityLevel::kWarning:
      return "Warning";
    case CompatibilityLevel::kError:
      return "Error";
  }
  return "Unknown";
}

CompatibilityResult TypeCompatibilityChecker::CheckAssignment(
    const Type& lhs, const Type& rhs) {
  // 1. Check for unknown types
  if (lhs.IsUnknown() || rhs.IsUnknown()) {
    return CompatibilityResult(CompatibilityLevel::kError,
                                "Cannot assign unknown type");
  }
  
  // 2. Exact match
  if (lhs == rhs) {
    return CompatibilityResult(CompatibilityLevel::kExact, "Types match exactly");
  }
  
  // 3. Check category compatibility first
  auto category_result = CheckCategoryCompatibility(lhs, rhs);
  if (category_result.IsError()) {
    return category_result;
  }
  
  // 4. Check width compatibility (skip for real types)
  CompatibilityResult width_result(CompatibilityLevel::kSafe, "");
  if (!lhs.IsReal() && !rhs.IsReal()) {
    width_result = CheckWidthCompatibility(lhs.GetWidth(), rhs.GetWidth());
  }
  
  // 5. Check sign compatibility
  auto sign_result = CheckSignCompatibility(lhs.is_signed, rhs.is_signed, &lhs, &rhs);
  
  // 6. Check state compatibility
  auto state_result = CheckStateCompatibility(lhs, rhs);
  
  // 7. Determine overall compatibility level
  // Take the most severe level
  CompatibilityLevel worst_level = CompatibilityLevel::kExact;
  std::ostringstream msg;
  
  if (category_result.level > worst_level) {
    worst_level = category_result.level;
    msg << category_result.message;
  }
  
  if (width_result.level > worst_level) {
    worst_level = width_result.level;
    if (msg.tellp() > 0) msg << "; ";
    msg << width_result.message;
  } else if (width_result.level == CompatibilityLevel::kWarning && 
             worst_level == CompatibilityLevel::kWarning) {
    if (msg.tellp() > 0) msg << "; ";
    msg << width_result.message;
  }
  
  if (sign_result.level > worst_level) {
    worst_level = sign_result.level;
    if (msg.tellp() > 0) msg << "; ";
    msg << sign_result.message;
  } else if (sign_result.level == CompatibilityLevel::kWarning && 
             worst_level == CompatibilityLevel::kWarning) {
    if (msg.tellp() > 0) msg << "; ";
    msg << sign_result.message;
  }
  
  if (state_result.level > worst_level) {
    worst_level = state_result.level;
    if (msg.tellp() > 0) msg << "; ";
    msg << state_result.message;
  } else if (state_result.level == CompatibilityLevel::kWarning && 
             worst_level == CompatibilityLevel::kWarning) {
    if (msg.tellp() > 0) msg << "; ";
    msg << state_result.message;
  }
  
  if (worst_level == CompatibilityLevel::kExact && 
      (width_result.level == CompatibilityLevel::kSafe || 
       state_result.level == CompatibilityLevel::kSafe)) {
    worst_level = CompatibilityLevel::kSafe;
  }
  
  return CompatibilityResult(worst_level, msg.str());
}

CompatibilityResult TypeCompatibilityChecker::CheckBinaryOp(
    const Type& lhs, const Type& rhs, BinaryOpType op) {
  // Check for unknown types
  if (lhs.IsUnknown() || rhs.IsUnknown()) {
    return CompatibilityResult(CompatibilityLevel::kError,
                                "Cannot operate on unknown type");
  }
  
  switch (op) {
    case BinaryOpType::kArithmetic:
      // Both operands must be numeric
      if (!lhs.IsNumeric() || !rhs.IsNumeric()) {
        return CompatibilityResult(CompatibilityLevel::kError,
                                    "Arithmetic operations require numeric types");
      }
      // Numeric types are compatible for arithmetic
      return CompatibilityResult(CompatibilityLevel::kSafe,
                                  "Numeric types compatible for arithmetic");
    
    case BinaryOpType::kBitwise:
      // Both operands must be integral
      if (!lhs.IsIntegral() || !rhs.IsIntegral()) {
        return CompatibilityResult(CompatibilityLevel::kError,
                                    "Bitwise operations require integral types");
      }
      return CompatibilityResult(CompatibilityLevel::kSafe,
                                  "Integral types compatible for bitwise operations");
    
    case BinaryOpType::kLogical:
      // Any type can be used in logical operations (treated as boolean)
      return CompatibilityResult(CompatibilityLevel::kSafe,
                                  "All types compatible for logical operations");
    
    case BinaryOpType::kComparison:
      // Types should be comparable (same category)
      {
        auto category_result = CheckCategoryCompatibility(lhs, rhs);
        if (category_result.IsError()) {
          return CompatibilityResult(CompatibilityLevel::kError,
                                      "Types not comparable");
        }
        return CompatibilityResult(CompatibilityLevel::kSafe,
                                    "Types compatible for comparison");
      }
    
    case BinaryOpType::kShift:
      // Left operand must be integral, right operand is shift amount
      if (!lhs.IsIntegral()) {
        return CompatibilityResult(CompatibilityLevel::kError,
                                    "Shift operations require integral left operand");
      }
      return CompatibilityResult(CompatibilityLevel::kSafe,
                                  "Type compatible for shift operation");
  }
  
  return CompatibilityResult(CompatibilityLevel::kError, "Unknown operation type");
}

CompatibilityResult TypeCompatibilityChecker::CheckWidthCompatibility(
    int lhs_width, int rhs_width) {
  if (lhs_width == rhs_width) {
    return CompatibilityResult(CompatibilityLevel::kExact, "Widths match exactly");
  }
  
  if (lhs_width > rhs_width) {
    // Widening: safe
    std::ostringstream msg;
    msg << "Safe widening from " << rhs_width << " to " << lhs_width << " bits";
    return CompatibilityResult(CompatibilityLevel::kSafe, msg.str());
  }
  
  // Narrowing: warning (potential truncation)
  std::ostringstream msg;
  msg << "Truncation from " << rhs_width << " to " << lhs_width << " bits";
  return CompatibilityResult(CompatibilityLevel::kWarning, msg.str());
}

CompatibilityResult TypeCompatibilityChecker::CheckSignCompatibility(
    bool lhs_signed, bool rhs_signed, const Type* lhs_type, const Type* rhs_type) {
  // Real types don't have signedness in the same way
  if ((lhs_type && lhs_type->IsReal()) || (rhs_type && rhs_type->IsReal())) {
    return CompatibilityResult(CompatibilityLevel::kSafe,
                                "Real types handle sign naturally");
  }
  
  if (lhs_signed == rhs_signed) {
    return CompatibilityResult(CompatibilityLevel::kExact, "Signedness matches");
  }
  
  if (lhs_signed && !rhs_signed) {
    return CompatibilityResult(CompatibilityLevel::kWarning,
                                "Assigning unsigned to signed (interpretation change)");
  }
  
  // !lhs_signed && rhs_signed
  return CompatibilityResult(CompatibilityLevel::kWarning,
                              "Assigning signed to unsigned (sign bit becomes value)");
}

CompatibilityResult TypeCompatibilityChecker::CheckStateCompatibility(
    const Type& lhs, const Type& rhs) {
  // Real types don't have 2-state/4-state distinction
  if (lhs.IsReal() || rhs.IsReal()) {
    return CompatibilityResult(CompatibilityLevel::kSafe,
                                "Real types don't have state distinction");
  }
  
  bool lhs_2state = lhs.Is2State();
  bool rhs_2state = rhs.Is2State();
  
  if (lhs_2state == rhs_2state) {
    return CompatibilityResult(CompatibilityLevel::kExact, "State matches");
  }
  
  if (!lhs_2state && rhs_2state) {
    // 2-state to 4-state: safe (0→0, 1→1)
    return CompatibilityResult(CompatibilityLevel::kSafe,
                                "Safe 2-state to 4-state conversion");
  }
  
  // 4-state to 2-state: warning (X/Z information lost)
  return CompatibilityResult(CompatibilityLevel::kWarning,
                              "4-state to 2-state conversion (X/Z become 0)");
}

CompatibilityResult TypeCompatibilityChecker::CheckCategoryCompatibility(
    const Type& lhs, const Type& rhs) {
  // 1. String type
  if (lhs.IsString() || rhs.IsString()) {
    if (lhs.IsString() && rhs.IsString()) {
      return CompatibilityResult(CompatibilityLevel::kExact, "Both strings");
    }
    return CompatibilityResult(CompatibilityLevel::kError,
                                "String incompatible with non-string");
  }
  
  // 2. User-defined types
  if (lhs.IsUserDefined() || rhs.IsUserDefined()) {
    if (lhs.IsUserDefined() && rhs.IsUserDefined()) {
      if (lhs.user_type_name == rhs.user_type_name) {
        return CompatibilityResult(CompatibilityLevel::kExact,
                                    "User-defined types match");
      }
      return CompatibilityResult(CompatibilityLevel::kError,
                                  "Different user-defined types");
    }
    return CompatibilityResult(CompatibilityLevel::kError,
                                "User-defined type incompatible with primitive");
  }
  
  // 3. Real and integral
  if (lhs.IsReal() && rhs.IsIntegral()) {
    return CompatibilityResult(CompatibilityLevel::kSafe,
                                "Integral to real (safe, possible precision consideration)");
  }
  
  if (lhs.IsIntegral() && rhs.IsReal()) {
    return CompatibilityResult(CompatibilityLevel::kWarning,
                                "Real to integral (precision loss, fractional part lost)");
  }
  
  // 4. Both integral or both real
  if ((lhs.IsIntegral() && rhs.IsIntegral()) ||
      (lhs.IsReal() && rhs.IsReal())) {
    return CompatibilityResult(CompatibilityLevel::kSafe, "Compatible categories");
  }
  
  // 5. Net types and regular types are compatible
  if ((lhs.IsNet() || lhs.IsIntegral()) && 
      (rhs.IsNet() || rhs.IsIntegral())) {
    return CompatibilityResult(CompatibilityLevel::kSafe,
                                "Net and logic types are compatible");
  }
  
  // Default: incompatible
  return CompatibilityResult(CompatibilityLevel::kError,
                              "Incompatible type categories");
}

Type TypeCompatibilityChecker::DetermineCommonType(
    const Type& lhs, const Type& rhs, BinaryOpType op) {
  // For arithmetic and bitwise operations, determine the common type
  // following IEEE 1800-2017 rules
  
  Type result;
  
  // 1. If either is real, result is real
  if (lhs.IsReal() || rhs.IsReal()) {
    result.base_type = PrimitiveType::kReal;
    return result;
  }
  
  // 2. Both are integral
  // Result width is max of operands (for bitwise)
  // or max + 1 (for arithmetic)
  int width = std::max(lhs.GetWidth(), rhs.GetWidth());
  
  if (op == BinaryOpType::kArithmetic) {
    width += 1;  // Add 1 bit for overflow
  }
  
  result.base_type = PrimitiveType::kLogic;
  result.dimensions = {width};
  
  // 3. Result is signed only if both operands are signed
  result.is_signed = lhs.is_signed && rhs.is_signed;
  
  // 4. Result is 4-state if either operand is 4-state
  if (lhs.Is4State() || rhs.Is4State()) {
    result.base_type = PrimitiveType::kLogic;  // 4-state
  } else {
    result.base_type = PrimitiveType::kBit;  // 2-state
  }
  
  return result;
}

}  // namespace analysis
}  // namespace verilog

