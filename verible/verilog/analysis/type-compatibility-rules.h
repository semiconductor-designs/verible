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

#ifndef VERIBLE_VERILOG_ANALYSIS_TYPE_COMPATIBILITY_RULES_H_
#define VERIBLE_VERILOG_ANALYSIS_TYPE_COMPATIBILITY_RULES_H_

#include <string>

#include "verible/verilog/analysis/type-representation.h"

namespace verilog {
namespace analysis {

// Result of compatibility check
enum class CompatibilityLevel {
  kExact,      // Types match exactly
  kSafe,       // Safe implicit conversion (e.g., 2-state to 4-state)
  kWarning,    // Conversion with potential issues (truncation, sign change)
  kError,      // Incompatible types (e.g., string to integer)
};

// Detailed result of compatibility analysis
struct CompatibilityResult {
  CompatibilityLevel level;
  std::string message;
  
  // Constructor
  CompatibilityResult(CompatibilityLevel lvl, std::string msg = "")
      : level(lvl), message(std::move(msg)) {}
  
  // Convenience checks
  bool IsOk() const { 
    return level == CompatibilityLevel::kExact || 
           level == CompatibilityLevel::kSafe; 
  }
  bool IsWarning() const { return level == CompatibilityLevel::kWarning; }
  bool IsError() const { return level == CompatibilityLevel::kError; }
  
  // Convert level to string
  std::string LevelToString() const;
};

// Type compatibility checker
// 
// Implements IEEE 1800-2017 type compatibility and conversion rules.
// Determines if values of one type can be assigned to variables of another type,
// and what warnings or errors should be generated.
//
// Usage:
//   TypeCompatibilityChecker checker;
//   auto result = checker.CheckAssignment(lhs_type, rhs_type);
//   if (result.IsWarning()) {
//     std::cerr << "Warning: " << result.message << "\n";
//   }
class TypeCompatibilityChecker {
 public:
  TypeCompatibilityChecker() = default;
  
  // Check if lhs can accept value of rhs type in an assignment.
  // This is the main compatibility check for assignments like: lhs = rhs;
  //
  // Returns:
  //   kExact: Types match exactly
  //   kSafe: Safe implicit conversion (e.g., narrower to wider, 2-state to 4-state)
  //   kWarning: Conversion with potential data loss (truncation, sign mismatch)
  //   kError: Incompatible types (e.g., string to integer)
  static CompatibilityResult CheckAssignment(const Type& lhs, const Type& rhs);
  
  // Check compatibility for binary operations: lhs op rhs
  // Different operators have different compatibility requirements.
  //
  // For arithmetic (+, -, *, /, %):
  //   - Both operands should be numeric
  //   - Types are promoted to a common type
  //
  // For bitwise (&, |, ^):
  //   - Both operands should be integral
  //   - Result width is max of operands
  //
  // For logical (&&, ||):
  //   - Any type can be used (treated as boolean)
  //   - Result is always 1-bit
  enum class BinaryOpType {
    kArithmetic,  // +, -, *, /, %
    kBitwise,     // &, |, ^
    kLogical,     // &&, ||
    kComparison,  // ==, !=, <, <=, >, >=
    kShift,       // <<, >>
  };
  
  static CompatibilityResult CheckBinaryOp(
      const Type& lhs, const Type& rhs, BinaryOpType op);
  
  // Check width compatibility for assignments and operations.
  //
  // Rules (IEEE 1800-2017):
  //   - Exact match: OK
  //   - Widening (8-bit -> 16-bit): Safe
  //   - Narrowing (16-bit -> 8-bit): Warning (truncation)
  static CompatibilityResult CheckWidthCompatibility(int lhs_width, int rhs_width);
  
  // Check sign compatibility for assignments and operations.
  //
  // Rules (IEEE 1800-2017):
  //   - Same signedness: OK
  //   - Unsigned to signed: Warning (interpretation change)
  //   - Signed to unsigned: Warning (sign bit becomes value)
  //   - Real types: Safe (sign handled naturally)
  static CompatibilityResult CheckSignCompatibility(
      bool lhs_signed, bool rhs_signed, 
      const Type* lhs_type = nullptr, const Type* rhs_type = nullptr);
  
  // Check state compatibility (2-state vs 4-state).
  //
  // Rules (IEEE 1800-2017):
  //   - 2-state to 2-state: OK
  //   - 4-state to 4-state: OK
  //   - 2-state to 4-state: Safe (0→0, 1→1)
  //   - 4-state to 2-state: Warning (X→0, Z→0, lose X/Z info)
  static CompatibilityResult CheckStateCompatibility(const Type& lhs, const Type& rhs);
  
  // Check type category compatibility.
  //
  // Categories:
  //   - Integral (bit, logic, int, etc.)
  //   - Real (real, realtime, shortreal)
  //   - String
  //   - User-defined (struct, enum, class)
  //
  // Rules:
  //   - Same category: OK (subject to width/sign checks)
  //   - Integral to real: Safe (with possible precision considerations)
  //   - Real to integral: Warning (precision loss, fractional part lost)
  //   - String assignments: Only string to string
  //   - User-defined: Exact match required
  static CompatibilityResult CheckCategoryCompatibility(const Type& lhs, const Type& rhs);
  
 private:
  // Helper: Determine common type for binary operations
  static Type DetermineCommonType(const Type& lhs, const Type& rhs, BinaryOpType op);
};

}  // namespace analysis
}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_TYPE_COMPATIBILITY_RULES_H_

