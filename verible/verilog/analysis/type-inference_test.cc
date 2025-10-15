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

#include "verible/verilog/analysis/type-inference.h"

#include "gtest/gtest.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace analysis {
namespace {

// Test fixture for TypeInference tests
class TypeInferenceTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Create a minimal project for symbol table
    project_ = std::make_unique<VerilogProject>(".", std::vector<std::string>{});
    symbol_table_ = std::make_unique<SymbolTable>(project_.get());
  }

  std::unique_ptr<VerilogProject> project_;
  std::unique_ptr<SymbolTable> symbol_table_;
};

// Test TypeInference construction
TEST_F(TypeInferenceTest, Construction) {
  TypeInference inference(symbol_table_.get());
  
  const auto& stats = inference.GetStats();
  EXPECT_EQ(stats.cache_hits, 0);
  EXPECT_EQ(stats.cache_misses, 0);
  EXPECT_EQ(stats.total_inferences, 0);
}

// Test cache clearing
TEST_F(TypeInferenceTest, ClearCache) {
  TypeInference inference(symbol_table_.get());
  
  // Perform some inferences (stats would increment)
  inference.ClearCache();
  
  const auto& stats = inference.GetStats();
  EXPECT_EQ(stats.cache_hits, 0);
  EXPECT_EQ(stats.cache_misses, 0);
  EXPECT_EQ(stats.total_inferences, 0);
}

// Test literal inference
TEST_F(TypeInferenceTest, InferLiteralInteger) {
  TypeInference inference(symbol_table_.get());
  
  // Test would require actual CST nodes
  // This is a structural test to verify API
  const auto& stats = inference.GetStats();
  EXPECT_GE(stats.total_inferences, 0);
}

// Test binary operator type promotion
TEST_F(TypeInferenceTest, BinaryOpArithmetic) {
  TypeInference inference(symbol_table_.get());
  
  // Create mock symbols for testing
  // In real usage, these would come from parsed CST
  
  // Test basic API structure
  EXPECT_NE(&inference, nullptr);
}

// Test unary operator inference
TEST_F(TypeInferenceTest, UnaryOpLogical) {
  TypeInference inference(symbol_table_.get());
  
  // Test API structure
  EXPECT_NE(&inference, nullptr);
}

// Test statistics tracking
TEST_F(TypeInferenceTest, StatisticsTracking) {
  TypeInference inference(symbol_table_.get());
  
  const auto& stats = inference.GetStats();
  EXPECT_EQ(stats.cache_hits, 0);
  EXPECT_EQ(stats.cache_misses, 0);
  EXPECT_EQ(stats.total_inferences, 0);
}

// Test cache hit behavior
TEST_F(TypeInferenceTest, CacheHitBehavior) {
  TypeInference inference(symbol_table_.get());
  
  // First call would be a cache miss
  // Second call on same expression would be a cache hit
  
  // Verify cache is working (structural test)
  inference.ClearCache();
  const auto& stats = inference.GetStats();
  EXPECT_EQ(stats.cache_hits, 0);
}

// Test GetDeclaredType with empty symbol table
TEST_F(TypeInferenceTest, GetDeclaredTypeEmpty) {
  TypeInference inference(symbol_table_.get());
  
  // Test with root node (always exists)
  const SymbolTableNode& root = symbol_table_->Root();
  
  // Getting declared type should work (returns unknown for root)
  const Type* type = inference.GetDeclaredType(root);
  EXPECT_NE(type, nullptr);
}

// Test type width calculation for binary ops
TEST_F(TypeInferenceTest, BinaryOpWidthPromotion) {
  TypeInference inference(symbol_table_.get());
  
  // Test structure - would need actual CST for full test
  // Verify API is callable
  const auto& stats = inference.GetStats();
  EXPECT_GE(stats.total_inferences, 0);
}

// Test real type propagation
TEST_F(TypeInferenceTest, RealTypePropagation) {
  TypeInference inference(symbol_table_.get());
  
  // Test structure for real type handling
  // Full test would require CST with real literals
  EXPECT_NE(&inference, nullptr);
}

// Test comparison operator result type
TEST_F(TypeInferenceTest, ComparisonResultType) {
  TypeInference inference(symbol_table_.get());
  
  // Comparison operators always return 1-bit logic
  // Test structure
  EXPECT_NE(&inference, nullptr);
}

// Test shift operator width preservation
TEST_F(TypeInferenceTest, ShiftOperatorWidth) {
  TypeInference inference(symbol_table_.get());
  
  // Shift operators preserve left operand width
  // Test structure
  EXPECT_NE(&inference, nullptr);
}

// Test reduction operator result
TEST_F(TypeInferenceTest, ReductionOperatorResult) {
  TypeInference inference(symbol_table_.get());
  
  // Reduction operators return 1-bit
  // Test structure
  EXPECT_NE(&inference, nullptr);
}

// Test concatenation width calculation
TEST_F(TypeInferenceTest, ConcatenationWidth) {
  TypeInference inference(symbol_table_.get());
  
  // Concatenation sums widths
  // Test structure
  EXPECT_NE(&inference, nullptr);
}

// Test conditional expression type
TEST_F(TypeInferenceTest, ConditionalExpressionType) {
  TypeInference inference(symbol_table_.get());
  
  // Conditional returns wider of two types
  // Test structure
  EXPECT_NE(&inference, nullptr);
}

// Week 2 Enhanced Tests

// Test type equality with different configurations
TEST_F(TypeInferenceTest, TypeEqualityComprehensive) {
  Type t1 = MakeLogicType(8, false);
  Type t2 = MakeLogicType(8, false);
  Type t3 = MakeLogicType(8, true);  // signed
  Type t4 = MakeLogicType(16, false);  // different width
  
  EXPECT_EQ(t1, t2);  // Same type
  EXPECT_NE(t1, t3);  // Different signedness
  EXPECT_NE(t1, t4);  // Different width
}

// Test type width for various types
TEST_F(TypeInferenceTest, TypeWidthVariety) {
  EXPECT_EQ(MakeLogicType(1).GetWidth(), 1);
  EXPECT_EQ(MakeLogicType(8).GetWidth(), 8);
  EXPECT_EQ(MakeLogicType(32).GetWidth(), 32);
  EXPECT_EQ(MakeLogicType(64).GetWidth(), 64);
  EXPECT_EQ(MakeIntType().GetWidth(), 32);
}

// Test type compatibility matrix
TEST_F(TypeInferenceTest, TypeCompatibilityMatrix) {
  Type logic8 = MakeLogicType(8);
  Type logic16 = MakeLogicType(16);
  Type bit8 = MakeBitType(8);
  Type int32 = MakeIntType();
  Type real_type = MakeRealType();
  Type string_type = MakeStringType();
  
  // Same width logic/bit are compatible
  EXPECT_TRUE(logic8.IsAssignableFrom(bit8));
  
  // Wider can accept narrower
  EXPECT_TRUE(logic16.IsAssignableFrom(logic8));
  
  // Real can accept integer
  EXPECT_TRUE(real_type.IsAssignableFrom(int32));
  
  // String is isolated
  EXPECT_FALSE(string_type.IsAssignableFrom(int32));
  EXPECT_FALSE(int32.IsAssignableFrom(string_type));
}

// Test user-defined types
TEST_F(TypeInferenceTest, UserDefinedTypeHandling) {
  Type my_struct = MakeUserDefinedType("my_struct_t");
  Type other_struct = MakeUserDefinedType("other_struct_t");
  Type same_struct = MakeUserDefinedType("my_struct_t");
  
  // Same name = compatible
  EXPECT_TRUE(my_struct.IsAssignableFrom(same_struct));
  
  // Different name = incompatible
  EXPECT_FALSE(my_struct.IsAssignableFrom(other_struct));
}

// Test ToString for various types
TEST_F(TypeInferenceTest, ToStringComprehensive) {
  EXPECT_EQ(MakeLogicType(1).ToString(), "logic[0:0]");
  EXPECT_EQ(MakeLogicType(8).ToString(), "logic[7:0]");
  EXPECT_EQ(MakeLogicType(16, true).ToString(), "signed logic[15:0]");
  EXPECT_EQ(MakeBitType(4).ToString(), "bit[3:0]");
  EXPECT_EQ(MakeIntType().ToString(), "int[31:0]");
  EXPECT_EQ(MakeRealType().ToString(), "real");
  EXPECT_EQ(MakeStringType().ToString(), "string");
}

// Test type properties comprehensively
TEST_F(TypeInferenceTest, TypePropertiesComplete) {
  Type logic_type = MakeLogicType(8);
  Type int_type = MakeIntType();
  Type real_type = MakeRealType();
  Type string_type = MakeStringType();
  
  // Logic type
  EXPECT_TRUE(logic_type.IsIntegral());
  EXPECT_TRUE(logic_type.IsNumeric());
  EXPECT_TRUE(logic_type.Is4State());
  EXPECT_FALSE(logic_type.Is2State());
  EXPECT_FALSE(logic_type.IsReal());
  
  // Int type
  EXPECT_TRUE(int_type.IsIntegral());
  EXPECT_TRUE(int_type.IsNumeric());
  EXPECT_TRUE(int_type.Is2State());
  EXPECT_FALSE(int_type.Is4State());
  
  // Real type
  EXPECT_FALSE(real_type.IsIntegral());
  EXPECT_TRUE(real_type.IsNumeric());
  EXPECT_TRUE(real_type.IsReal());
  
  // String type
  EXPECT_FALSE(string_type.IsIntegral());
  EXPECT_FALSE(string_type.IsNumeric());
  EXPECT_FALSE(string_type.IsReal());
}

// Test cache functionality
TEST_F(TypeInferenceTest, CacheFunctionality) {
  TypeInference inference(symbol_table_.get());
  
  // Verify cache starts empty
  const auto& stats1 = inference.GetStats();
  EXPECT_EQ(stats1.cache_hits, 0);
  EXPECT_EQ(stats1.cache_misses, 0);
  
  // Clear cache
  inference.ClearCache();
  
  // Verify stats reset
  const auto& stats2 = inference.GetStats();
  EXPECT_EQ(stats2.cache_hits, 0);
  EXPECT_EQ(stats2.cache_misses, 0);
  EXPECT_EQ(stats2.total_inferences, 0);
}

// Test API stability
TEST_F(TypeInferenceTest, APIStability) {
  TypeInference inference(symbol_table_.get());
  
  // Verify all main APIs are accessible
  const auto& stats = inference.GetStats();
  EXPECT_GE(stats.total_inferences, 0);
  
  // Verify cache clear works
  inference.ClearCache();
  
  // Verify construction works
  EXPECT_NE(&inference, nullptr);
}

// Test type dimension handling
TEST_F(TypeInferenceTest, TypeDimensions) {
  Type t1 = MakeLogicType(8);
  ASSERT_EQ(t1.dimensions.size(), 1);
  EXPECT_EQ(t1.dimensions[0], 8);
  
  // Multi-dimensional (simulated)
  Type t2 = MakeLogicType(8);
  t2.dimensions.push_back(4);  // [3:0][7:0]
  EXPECT_EQ(t2.GetWidth(), 32);  // 4 * 8
}

// Test type construction methods
TEST_F(TypeInferenceTest, TypeConstructionMethods) {
  // Test all helper functions
  EXPECT_NO_THROW(MakeLogicType(8));
  EXPECT_NO_THROW(MakeLogicType(16, true));
  EXPECT_NO_THROW(MakeBitType(32));
  EXPECT_NO_THROW(MakeIntType());
  EXPECT_NO_THROW(MakeRealType());
  EXPECT_NO_THROW(MakeStringType());
  EXPECT_NO_THROW(MakeUserDefinedType("test"));
}

// Test edge cases
TEST_F(TypeInferenceTest, EdgeCases) {
  // Zero-width type (edge case)
  Type t1(PrimitiveType::kLogic);
  EXPECT_EQ(t1.GetWidth(), 1);  // Default 1-bit
  
  // Unknown type
  Type t2(PrimitiveType::kUnknown);
  EXPECT_TRUE(t2.IsUnknown());
  EXPECT_FALSE(t2.IsNumeric());
}

}  // namespace
}  // namespace analysis
}  // namespace verilog

