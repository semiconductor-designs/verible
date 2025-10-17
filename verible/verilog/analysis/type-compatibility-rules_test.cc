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

#include "gtest/gtest.h"
#include "verible/verilog/analysis/type-representation.h"

namespace verilog {
namespace analysis {
namespace {

// ============================================================================
// WEEK 3: TYPE COMPATIBILITY RULES TESTS (25+ TESTS)
// ============================================================================

// ----------------------------------------------------------------------------
// Category 1: Width Compatibility (8 tests)
// ----------------------------------------------------------------------------

TEST(TypeCompatibilityTest, WidthExactMatch) {
  // Test: logic [7:0] = logic [7:0]
  auto result = TypeCompatibilityChecker::CheckWidthCompatibility(8, 8);
  
  EXPECT_TRUE(result.IsOk());
  EXPECT_EQ(result.level, CompatibilityLevel::kExact);
}

TEST(TypeCompatibilityTest, WidthWidening) {
  // Test: logic [15:0] = logic [7:0] (safe widening)
  auto result = TypeCompatibilityChecker::CheckWidthCompatibility(16, 8);
  
  EXPECT_TRUE(result.IsOk());
  EXPECT_EQ(result.level, CompatibilityLevel::kSafe);
  EXPECT_NE(result.message.find("widening"), std::string::npos);
}

TEST(TypeCompatibilityTest, WidthNarrowing) {
  // Test: logic [7:0] = logic [15:0] (truncation warning)
  auto result = TypeCompatibilityChecker::CheckWidthCompatibility(8, 16);
  
  EXPECT_TRUE(result.IsWarning());
  EXPECT_EQ(result.level, CompatibilityLevel::kWarning);
  EXPECT_NE(result.message.find("Truncation"), std::string::npos);
}

TEST(TypeCompatibilityTest, WidthLargeWidening) {
  // Test: logic [63:0] = logic [7:0] (large widening)
  auto result = TypeCompatibilityChecker::CheckWidthCompatibility(64, 8);
  
  EXPECT_TRUE(result.IsOk());
  EXPECT_EQ(result.level, CompatibilityLevel::kSafe);
}

TEST(TypeCompatibilityTest, WidthOneToMany) {
  // Test: logic [31:0] = logic [0] (1-bit to 32-bit)
  auto result = TypeCompatibilityChecker::CheckWidthCompatibility(32, 1);
  
  EXPECT_TRUE(result.IsOk());
  EXPECT_EQ(result.level, CompatibilityLevel::kSafe);
}

TEST(TypeCompatibilityTest, WidthSevereTruncation) {
  // Test: logic [3:0] = logic [31:0] (severe truncation)
  auto result = TypeCompatibilityChecker::CheckWidthCompatibility(4, 32);
  
  EXPECT_TRUE(result.IsWarning());
  EXPECT_EQ(result.level, CompatibilityLevel::kWarning);
}

TEST(TypeCompatibilityTest, WidthSlightNarrowing) {
  // Test: logic [7:0] = logic [8:0] (1-bit truncation)
  auto result = TypeCompatibilityChecker::CheckWidthCompatibility(8, 9);
  
  EXPECT_TRUE(result.IsWarning());
}

TEST(TypeCompatibilityTest, WidthStandardSizes) {
  // Test: Various standard sizes
  EXPECT_TRUE(TypeCompatibilityChecker::CheckWidthCompatibility(8, 8).IsOk());
  EXPECT_TRUE(TypeCompatibilityChecker::CheckWidthCompatibility(16, 16).IsOk());
  EXPECT_TRUE(TypeCompatibilityChecker::CheckWidthCompatibility(32, 32).IsOk());
  EXPECT_TRUE(TypeCompatibilityChecker::CheckWidthCompatibility(64, 64).IsOk());
}

// ----------------------------------------------------------------------------
// Category 2: Sign Compatibility (8 tests)
// ----------------------------------------------------------------------------

TEST(TypeCompatibilityTest, SignBothSigned) {
  // Test: signed = signed
  auto result = TypeCompatibilityChecker::CheckSignCompatibility(true, true);
  
  EXPECT_TRUE(result.IsOk());
  EXPECT_EQ(result.level, CompatibilityLevel::kExact);
}

TEST(TypeCompatibilityTest, SignBothUnsigned) {
  // Test: unsigned = unsigned
  auto result = TypeCompatibilityChecker::CheckSignCompatibility(false, false);
  
  EXPECT_TRUE(result.IsOk());
  EXPECT_EQ(result.level, CompatibilityLevel::kExact);
}

TEST(TypeCompatibilityTest, SignUnsignedToSigned) {
  // Test: signed = unsigned (interpretation change warning)
  auto result = TypeCompatibilityChecker::CheckSignCompatibility(true, false);
  
  EXPECT_TRUE(result.IsWarning());
  EXPECT_EQ(result.level, CompatibilityLevel::kWarning);
  EXPECT_NE(result.message.find("unsigned to signed"), std::string::npos);
}

TEST(TypeCompatibilityTest, SignSignedToUnsigned) {
  // Test: unsigned = signed (sign bit becomes value warning)
  auto result = TypeCompatibilityChecker::CheckSignCompatibility(false, true);
  
  EXPECT_TRUE(result.IsWarning());
  EXPECT_EQ(result.level, CompatibilityLevel::kWarning);
  EXPECT_NE(result.message.find("signed to unsigned"), std::string::npos);
}

TEST(TypeCompatibilityTest, SignComprehensive) {
  // Test all combinations
  EXPECT_TRUE(TypeCompatibilityChecker::CheckSignCompatibility(true, true).IsOk());
  EXPECT_TRUE(TypeCompatibilityChecker::CheckSignCompatibility(false, false).IsOk());
  EXPECT_TRUE(TypeCompatibilityChecker::CheckSignCompatibility(true, false).IsWarning());
  EXPECT_TRUE(TypeCompatibilityChecker::CheckSignCompatibility(false, true).IsWarning());
}

TEST(TypeCompatibilityTest, SignDefaultUnsigned) {
  // Test: Default is unsigned
  Type unsigned_type = MakeLogicType(8, false);
  Type signed_type = MakeLogicType(8, true);
  
  EXPECT_FALSE(unsigned_type.is_signed);
  EXPECT_TRUE(signed_type.is_signed);
}

TEST(TypeCompatibilityTest, SignArithmeticImpact) {
  // Test: Sign affects arithmetic operations
  Type a_unsigned = MakeLogicType(8, false);
  Type b_signed = MakeLogicType(8, true);
  
  EXPECT_FALSE(a_unsigned.is_signed);
  EXPECT_TRUE(b_signed.is_signed);
}

TEST(TypeCompatibilityTest, SignPreservation) {
  // Test: Sign should be preserved in type system
  Type signed_8 = MakeLogicType(8, true);
  Type unsigned_8 = MakeLogicType(8, false);
  
  EXPECT_NE(signed_8, unsigned_8);  // Different types due to sign
}

// ----------------------------------------------------------------------------
// Category 3: State Compatibility (5 tests)
// ----------------------------------------------------------------------------

TEST(TypeCompatibilityTest, State2To4Safe) {
  // Test: logic (4-state) = bit (2-state) [safe]
  Type logic_type = MakeLogicType(8);  // 4-state
  Type bit_type = MakeBitType(8);      // 2-state
  
  auto result = TypeCompatibilityChecker::CheckStateCompatibility(logic_type, bit_type);
  
  EXPECT_TRUE(result.IsOk());
  EXPECT_EQ(result.level, CompatibilityLevel::kSafe);
}

TEST(TypeCompatibilityTest, State4To2Warning) {
  // Test: bit (2-state) = logic (4-state) [warning: X/Z lost]
  Type bit_type = MakeBitType(8);      // 2-state
  Type logic_type = MakeLogicType(8);  // 4-state
  
  auto result = TypeCompatibilityChecker::CheckStateCompatibility(bit_type, logic_type);
  
  EXPECT_TRUE(result.IsWarning());
  EXPECT_EQ(result.level, CompatibilityLevel::kWarning);
  EXPECT_NE(result.message.find("X/Z"), std::string::npos);
}

TEST(TypeCompatibilityTest, StateSameState) {
  // Test: Same state is exact match
  Type logic1 = MakeLogicType(8);
  Type logic2 = MakeLogicType(16);
  
  auto result = TypeCompatibilityChecker::CheckStateCompatibility(logic1, logic2);
  EXPECT_TRUE(result.IsOk());
}

TEST(TypeCompatibilityTest, StateIntVsLogic) {
  // Test: int (2-state) vs logic (4-state)
  Type int_type = MakeIntType();      // 2-state
  Type logic_type = MakeLogicType(32); // 4-state
  
  EXPECT_TRUE(int_type.Is2State());
  EXPECT_TRUE(logic_type.Is4State());
}

TEST(TypeCompatibilityTest, StatePreservation) {
  // Test: 4-state logic preserves X and Z
  Type logic_type = MakeLogicType(8);
  EXPECT_TRUE(logic_type.Is4State());
  EXPECT_FALSE(logic_type.Is2State());
}

// ----------------------------------------------------------------------------
// Category 4: Category Compatibility (4 tests)
// ----------------------------------------------------------------------------

TEST(TypeCompatibilityTest, CategoryIntegralToReal) {
  // Test: real = int (safe, possible precision consideration)
  Type real_type = MakeRealType();
  Type int_type = MakeIntType();
  
  auto result = TypeCompatibilityChecker::CheckCategoryCompatibility(real_type, int_type);
  
  EXPECT_TRUE(result.IsOk());
  EXPECT_EQ(result.level, CompatibilityLevel::kSafe);
}

TEST(TypeCompatibilityTest, CategoryRealToIntegral) {
  // Test: int = real (warning: precision loss)
  Type int_type = MakeIntType();
  Type real_type = MakeRealType();
  
  auto result = TypeCompatibilityChecker::CheckCategoryCompatibility(int_type, real_type);
  
  EXPECT_TRUE(result.IsWarning());
  EXPECT_NE(result.message.find("precision loss"), std::string::npos);
}

TEST(TypeCompatibilityTest, CategoryStringIsolated) {
  // Test: string is incompatible with non-string
  Type string_type = MakeStringType();
  Type int_type = MakeIntType();
  
  auto result = TypeCompatibilityChecker::CheckCategoryCompatibility(string_type, int_type);
  
  EXPECT_TRUE(result.IsError());
}

TEST(TypeCompatibilityTest, CategoryUserDefinedExact) {
  // Test: User-defined types must match exactly
  Type type1 = MakeUserDefinedType("my_struct_t");
  Type type2 = MakeUserDefinedType("my_struct_t");
  Type type3 = MakeUserDefinedType("other_struct_t");
  
  auto result1 = TypeCompatibilityChecker::CheckCategoryCompatibility(type1, type2);
  EXPECT_TRUE(result1.IsOk());
  
  auto result2 = TypeCompatibilityChecker::CheckCategoryCompatibility(type1, type3);
  EXPECT_TRUE(result2.IsError());
}

// ----------------------------------------------------------------------------
// Category 5: Full Assignment Compatibility (10+ tests)
// ----------------------------------------------------------------------------

TEST(TypeCompatibilityTest, AssignmentExactMatch) {
  // Test: logic [7:0] = logic [7:0]
  Type lhs = MakeLogicType(8);
  Type rhs = MakeLogicType(8);
  
  auto result = TypeCompatibilityChecker::CheckAssignment(lhs, rhs);
  
  EXPECT_TRUE(result.IsOk());
  EXPECT_EQ(result.level, CompatibilityLevel::kExact);
}

TEST(TypeCompatibilityTest, AssignmentSafeWidening) {
  // Test: logic [15:0] = logic [7:0]
  Type lhs = MakeLogicType(16);
  Type rhs = MakeLogicType(8);
  
  auto result = TypeCompatibilityChecker::CheckAssignment(lhs, rhs);
  
  EXPECT_TRUE(result.IsOk());
}

TEST(TypeCompatibilityTest, AssignmentTruncation) {
  // Test: logic [7:0] = logic [15:0] (truncation warning)
  Type lhs = MakeLogicType(8);
  Type rhs = MakeLogicType(16);
  
  auto result = TypeCompatibilityChecker::CheckAssignment(lhs, rhs);
  
  EXPECT_TRUE(result.IsWarning());
  EXPECT_NE(result.message.find("Truncation"), std::string::npos);
}

TEST(TypeCompatibilityTest, AssignmentSignMismatch) {
  // Test: unsigned = signed (warning)
  Type lhs = MakeLogicType(8, false);  // unsigned
  Type rhs = MakeLogicType(8, true);   // signed
  
  auto result = TypeCompatibilityChecker::CheckAssignment(lhs, rhs);
  
  EXPECT_TRUE(result.IsWarning());
}

TEST(TypeCompatibilityTest, AssignmentStateMismatch) {
  // Test: bit = logic (4-state to 2-state warning)
  Type lhs = MakeBitType(8);      // 2-state
  Type rhs = MakeLogicType(8);    // 4-state
  
  auto result = TypeCompatibilityChecker::CheckAssignment(lhs, rhs);
  
  EXPECT_TRUE(result.IsWarning());
}

TEST(TypeCompatibilityTest, AssignmentMultipleWarnings) {
  // Test: Multiple issues (truncation + sign mismatch)
  Type lhs = MakeLogicType(8, false);   // 8-bit unsigned
  Type rhs = MakeLogicType(16, true);   // 16-bit signed
  
  auto result = TypeCompatibilityChecker::CheckAssignment(lhs, rhs);
  
  EXPECT_TRUE(result.IsWarning());
  // Should mention both truncation and sign issues
}

TEST(TypeCompatibilityTest, AssignmentStringError) {
  // Test: int = string (error)
  Type lhs = MakeIntType();
  Type rhs = MakeStringType();
  
  auto result = TypeCompatibilityChecker::CheckAssignment(lhs, rhs);
  
  EXPECT_TRUE(result.IsError());
}

TEST(TypeCompatibilityTest, AssignmentRealToInt) {
  // Test: int = real (warning: precision loss)
  Type lhs = MakeIntType();
  Type rhs = MakeRealType();
  
  auto result = TypeCompatibilityChecker::CheckAssignment(lhs, rhs);
  
  EXPECT_TRUE(result.IsWarning());
}

TEST(TypeCompatibilityTest, AssignmentIntToReal) {
  // Test: real = int (safe)
  Type lhs = MakeRealType();
  Type rhs = MakeIntType();
  
  auto result = TypeCompatibilityChecker::CheckAssignment(lhs, rhs);
  
  EXPECT_TRUE(result.IsOk());
}

TEST(TypeCompatibilityTest, AssignmentUserDefinedMismatch) {
  // Test: Different user-defined types (error)
  Type lhs = MakeUserDefinedType("struct_a");
  Type rhs = MakeUserDefinedType("struct_b");
  
  auto result = TypeCompatibilityChecker::CheckAssignment(lhs, rhs);
  
  EXPECT_TRUE(result.IsError());
}

// ----------------------------------------------------------------------------
// Category 6: Binary Operation Compatibility (5+ tests)
// ----------------------------------------------------------------------------

TEST(TypeCompatibilityTest, BinaryOpArithmetic) {
  // Test: Arithmetic operations require numeric types
  Type int1 = MakeIntType();
  Type int2 = MakeIntType();
  
  auto result = TypeCompatibilityChecker::CheckBinaryOp(
      int1, int2, TypeCompatibilityChecker::BinaryOpType::kArithmetic);
  
  EXPECT_TRUE(result.IsOk());
}

TEST(TypeCompatibilityTest, BinaryOpBitwise) {
  // Test: Bitwise operations require integral types
  Type logic1 = MakeLogicType(8);
  Type logic2 = MakeLogicType(8);
  
  auto result = TypeCompatibilityChecker::CheckBinaryOp(
      logic1, logic2, TypeCompatibilityChecker::BinaryOpType::kBitwise);
  
  EXPECT_TRUE(result.IsOk());
}

TEST(TypeCompatibilityTest, BinaryOpLogical) {
  // Test: Logical operations accept any type
  Type int_type = MakeIntType();
  Type string_type = MakeStringType();
  
  auto result = TypeCompatibilityChecker::CheckBinaryOp(
      int_type, string_type, TypeCompatibilityChecker::BinaryOpType::kLogical);
  
  EXPECT_TRUE(result.IsOk());  // Logical operations are lenient
}

TEST(TypeCompatibilityTest, BinaryOpStringArithmetic) {
  // Test: String in arithmetic (error)
  Type string_type = MakeStringType();
  Type int_type = MakeIntType();
  
  auto result = TypeCompatibilityChecker::CheckBinaryOp(
      string_type, int_type, TypeCompatibilityChecker::BinaryOpType::kArithmetic);
  
  EXPECT_TRUE(result.IsError());
}

TEST(TypeCompatibilityTest, BinaryOpRealArithmetic) {
  // Test: Real in arithmetic (OK)
  Type real_type = MakeRealType();
  Type int_type = MakeIntType();
  
  auto result = TypeCompatibilityChecker::CheckBinaryOp(
      real_type, int_type, TypeCompatibilityChecker::BinaryOpType::kArithmetic);
  
  EXPECT_TRUE(result.IsOk());
}

// ----------------------------------------------------------------------------
// Edge Cases & Integration (5+ tests)
// ----------------------------------------------------------------------------

TEST(TypeCompatibilityTest, CompatibilityResultToString) {
  // Test: CompatibilityResult level to string
  CompatibilityResult exact(CompatibilityLevel::kExact);
  CompatibilityResult safe(CompatibilityLevel::kSafe);
  CompatibilityResult warning(CompatibilityLevel::kWarning);
  CompatibilityResult error(CompatibilityLevel::kError);
  
  EXPECT_EQ(exact.LevelToString(), "Exact");
  EXPECT_EQ(safe.LevelToString(), "Safe");
  EXPECT_EQ(warning.LevelToString(), "Warning");
  EXPECT_EQ(error.LevelToString(), "Error");
}

TEST(TypeCompatibilityTest, CompatibilityIsOk) {
  // Test: IsOk() checks
  EXPECT_TRUE(CompatibilityResult(CompatibilityLevel::kExact).IsOk());
  EXPECT_TRUE(CompatibilityResult(CompatibilityLevel::kSafe).IsOk());
  EXPECT_FALSE(CompatibilityResult(CompatibilityLevel::kWarning).IsOk());
  EXPECT_FALSE(CompatibilityResult(CompatibilityLevel::kError).IsOk());
}

TEST(TypeCompatibilityTest, UnknownTypeAssignment) {
  // Test: Unknown type handling
  Type unknown(PrimitiveType::kUnknown);
  Type known = MakeIntType();
  
  auto result = TypeCompatibilityChecker::CheckAssignment(unknown, known);
  EXPECT_TRUE(result.IsError());
}

TEST(TypeCompatibilityTest, ComplexAssignmentScenario) {
  // Test: Real-world complex scenario
  // bit [7:0] = logic [15:0] signed
  // Issues: truncation, state mismatch
  Type lhs = MakeBitType(8);           // 8-bit, 2-state, unsigned
  Type rhs = MakeLogicType(16, true);  // 16-bit, 4-state, signed
  
  auto result = TypeCompatibilityChecker::CheckAssignment(lhs, rhs);
  
  EXPECT_TRUE(result.IsWarning());
  // Should have multiple warnings
}

TEST(TypeCompatibilityTest, IdenticalTypesAllOk) {
  // Test: Identical types are always OK
  Type t1 = MakeLogicType(8);
  Type t2 = MakeLogicType(8);
  
  auto result = TypeCompatibilityChecker::CheckAssignment(t1, t2);
  EXPECT_EQ(result.level, CompatibilityLevel::kExact);
}

}  // namespace
}  // namespace analysis
}  // namespace verilog

