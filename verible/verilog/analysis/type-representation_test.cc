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

#include "verible/verilog/analysis/type-representation.h"

#include "gtest/gtest.h"

namespace verilog {
namespace analysis {
namespace {

// Test Type construction
TEST(TypeRepresentationTest, DefaultConstruction) {
  Type t;
  EXPECT_EQ(t.base_type, PrimitiveType::kUnknown);
  EXPECT_FALSE(t.is_signed);
  EXPECT_FALSE(t.is_packed);
  EXPECT_TRUE(t.dimensions.empty());
}

TEST(TypeRepresentationTest, PrimitiveTypeConstruction) {
  Type t(PrimitiveType::kLogic);
  EXPECT_EQ(t.base_type, PrimitiveType::kLogic);
  EXPECT_EQ(t.GetWidth(), 1);
}

TEST(TypeRepresentationTest, PrimitiveTypeWithWidth) {
  Type t(PrimitiveType::kLogic, 8);
  EXPECT_EQ(t.base_type, PrimitiveType::kLogic);
  ASSERT_EQ(t.dimensions.size(), 1);
  EXPECT_EQ(t.dimensions[0], 8);
  EXPECT_EQ(t.GetWidth(), 8);
}

// Test helper functions
TEST(TypeRepresentationTest, MakeLogicType) {
  Type t = MakeLogicType(16, true);
  EXPECT_EQ(t.base_type, PrimitiveType::kLogic);
  EXPECT_TRUE(t.is_signed);
  EXPECT_EQ(t.GetWidth(), 16);
}

TEST(TypeRepresentationTest, MakeBitType) {
  Type t = MakeBitType(32);
  EXPECT_EQ(t.base_type, PrimitiveType::kBit);
  EXPECT_FALSE(t.is_signed);
  EXPECT_EQ(t.GetWidth(), 32);
}

TEST(TypeRepresentationTest, MakeIntType) {
  Type t = MakeIntType();
  EXPECT_EQ(t.base_type, PrimitiveType::kInt);
  EXPECT_EQ(t.GetWidth(), 32);
}

TEST(TypeRepresentationTest, MakeRealType) {
  Type t = MakeRealType();
  EXPECT_EQ(t.base_type, PrimitiveType::kReal);
  EXPECT_TRUE(t.IsReal());
}

TEST(TypeRepresentationTest, MakeStringType) {
  Type t = MakeStringType();
  EXPECT_EQ(t.base_type, PrimitiveType::kString);
}

TEST(TypeRepresentationTest, MakeUserDefinedType) {
  Type t = MakeUserDefinedType("my_struct_t");
  EXPECT_EQ(t.base_type, PrimitiveType::kUserDefined);
  EXPECT_EQ(t.user_type_name, "my_struct_t");
}

// Test ToString
TEST(TypeRepresentationTest, ToStringLogic) {
  Type t = MakeLogicType(8);
  EXPECT_EQ(t.ToString(), "logic[7:0]");
}

TEST(TypeRepresentationTest, ToStringSignedLogic) {
  Type t = MakeLogicType(16, true);
  EXPECT_EQ(t.ToString(), "signed logic[15:0]");
}

TEST(TypeRepresentationTest, ToStringInt) {
  Type t = MakeIntType();
  EXPECT_EQ(t.ToString(), "int[31:0]");
}

TEST(TypeRepresentationTest, ToStringUserDefined) {
  Type t = MakeUserDefinedType("packet_t");
  EXPECT_EQ(t.ToString(), "packet_t");
}

// Test type properties
TEST(TypeRepresentationTest, IsNumeric) {
  EXPECT_TRUE(MakeIntType().IsNumeric());
  EXPECT_TRUE(MakeRealType().IsNumeric());
  EXPECT_TRUE(MakeLogicType(8).IsNumeric());
  EXPECT_FALSE(MakeStringType().IsNumeric());
}

TEST(TypeRepresentationTest, IsIntegral) {
  EXPECT_TRUE(MakeIntType().IsIntegral());
  EXPECT_TRUE(MakeLogicType(8).IsIntegral());
  EXPECT_FALSE(MakeRealType().IsIntegral());
  EXPECT_FALSE(MakeStringType().IsIntegral());
}

TEST(TypeRepresentationTest, Is2State) {
  Type bit_type(PrimitiveType::kBit);
  Type int_type = MakeIntType();
  Type logic_type = MakeLogicType(8);
  
  EXPECT_TRUE(bit_type.Is2State());
  EXPECT_TRUE(int_type.Is2State());
  EXPECT_FALSE(logic_type.Is2State());
}

TEST(TypeRepresentationTest, Is4State) {
  Type logic_type = MakeLogicType(8);
  Type reg_type(PrimitiveType::kReg);
  Type bit_type(PrimitiveType::kBit);
  
  EXPECT_TRUE(logic_type.Is4State());
  EXPECT_TRUE(reg_type.Is4State());
  EXPECT_FALSE(bit_type.Is4State());
}

TEST(TypeRepresentationTest, IsReal) {
  EXPECT_TRUE(MakeRealType().IsReal());
  EXPECT_TRUE(Type(PrimitiveType::kShortReal).IsReal());
  EXPECT_FALSE(MakeIntType().IsReal());
}

TEST(TypeRepresentationTest, IsNet) {
  Type wire(PrimitiveType::kWire);
  Type tri(PrimitiveType::kTri);
  Type logic = MakeLogicType(8);
  
  EXPECT_TRUE(wire.IsNet());
  EXPECT_TRUE(tri.IsNet());
  EXPECT_FALSE(logic.IsNet());
}

// Test GetWidth
TEST(TypeRepresentationTest, GetWidthDefaultTypes) {
  EXPECT_EQ(MakeLogicType(1).GetWidth(), 1);
  EXPECT_EQ(MakeLogicType(8).GetWidth(), 8);
  EXPECT_EQ(MakeIntType().GetWidth(), 32);
  EXPECT_EQ(Type(PrimitiveType::kByte).GetWidth(), 8);
  EXPECT_EQ(Type(PrimitiveType::kShortInt).GetWidth(), 16);
}

TEST(TypeRepresentationTest, GetWidthMultipleDimensions) {
  Type t = MakeLogicType(8);
  t.dimensions.push_back(4);  // [3:0][7:0]
  EXPECT_EQ(t.GetWidth(), 32);  // 4 * 8
}

// Test type equality
TEST(TypeRepresentationTest, EqualityExactMatch) {
  Type t1 = MakeLogicType(8);
  Type t2 = MakeLogicType(8);
  EXPECT_EQ(t1, t2);
}

TEST(TypeRepresentationTest, EqualityDifferentWidth) {
  Type t1 = MakeLogicType(8);
  Type t2 = MakeLogicType(16);
  EXPECT_NE(t1, t2);
}

TEST(TypeRepresentationTest, EqualityDifferentSignedness) {
  Type t1 = MakeLogicType(8, false);
  Type t2 = MakeLogicType(8, true);
  EXPECT_NE(t1, t2);
}

// Test IsAssignableFrom
TEST(TypeRepresentationTest, IsAssignableFromExactMatch) {
  Type t1 = MakeLogicType(8);
  Type t2 = MakeLogicType(8);
  EXPECT_TRUE(t1.IsAssignableFrom(t2));
}

TEST(TypeRepresentationTest, IsAssignableFromSameWidth) {
  Type logic8 = MakeLogicType(8);
  Type bit8 = MakeBitType(8);
  EXPECT_TRUE(logic8.IsAssignableFrom(bit8));
}

TEST(TypeRepresentationTest, IsAssignableFromWiderTarget) {
  Type logic16 = MakeLogicType(16);
  Type logic8 = MakeLogicType(8);
  EXPECT_TRUE(logic16.IsAssignableFrom(logic8));
}

TEST(TypeRepresentationTest, IsAssignableFromNarrowerTarget) {
  Type logic8 = MakeLogicType(8);
  Type logic16 = MakeLogicType(16);
  // Allowed with truncation warning
  EXPECT_TRUE(logic8.IsAssignableFrom(logic16));
}

TEST(TypeRepresentationTest, IsAssignableFromRealToInteger) {
  Type real_type = MakeRealType();
  Type int_type = MakeIntType();
  EXPECT_TRUE(real_type.IsAssignableFrom(int_type));
}

TEST(TypeRepresentationTest, IsAssignableFromIntegerToReal) {
  Type int_type = MakeIntType();
  Type real_type = MakeRealType();
  EXPECT_FALSE(int_type.IsAssignableFrom(real_type));
}

TEST(TypeRepresentationTest, IsAssignableFromStringToString) {
  Type str1 = MakeStringType();
  Type str2 = MakeStringType();
  EXPECT_TRUE(str1.IsAssignableFrom(str2));
}

TEST(TypeRepresentationTest, IsAssignableFromStringToInt) {
  Type str = MakeStringType();
  Type int_type = MakeIntType();
  EXPECT_FALSE(str.IsAssignableFrom(int_type));
}

TEST(TypeRepresentationTest, IsAssignableFromUserDefined) {
  Type t1 = MakeUserDefinedType("my_type");
  Type t2 = MakeUserDefinedType("my_type");
  Type t3 = MakeUserDefinedType("other_type");
  
  EXPECT_TRUE(t1.IsAssignableFrom(t2));
  EXPECT_FALSE(t1.IsAssignableFrom(t3));
}

TEST(TypeRepresentationTest, IsAssignableFromUnknown) {
  Type unknown;
  Type logic8 = MakeLogicType(8);
  
  EXPECT_FALSE(logic8.IsAssignableFrom(unknown));
  EXPECT_FALSE(unknown.IsAssignableFrom(logic8));
}

// Test PrimitiveTypeToString
TEST(TypeRepresentationTest, PrimitiveTypeToString) {
  EXPECT_EQ(PrimitiveTypeToString(PrimitiveType::kLogic), "logic");
  EXPECT_EQ(PrimitiveTypeToString(PrimitiveType::kBit), "bit");
  EXPECT_EQ(PrimitiveTypeToString(PrimitiveType::kInt), "int");
  EXPECT_EQ(PrimitiveTypeToString(PrimitiveType::kReal), "real");
  EXPECT_EQ(PrimitiveTypeToString(PrimitiveType::kString), "string");
  EXPECT_EQ(PrimitiveTypeToString(PrimitiveType::kUnknown), "<unknown>");
}

}  // namespace
}  // namespace analysis
}  // namespace verilog

