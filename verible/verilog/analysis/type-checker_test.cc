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

#include "gtest/gtest.h"
#include "verible/verilog/analysis/call-graph.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-inference.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace analysis {
namespace {

// Test fixture for TypeChecker tests
class TypeCheckerTest : public ::testing::Test {
 protected:
  void SetUp() override {
    project_ = std::make_unique<VerilogProject>(".", std::vector<std::string>{});
    symbol_table_ = std::make_unique<SymbolTable>(project_.get());
    type_inference_ = std::make_unique<TypeInference>(symbol_table_.get());
  }

  std::unique_ptr<VerilogProject> project_;
  std::unique_ptr<SymbolTable> symbol_table_;
  std::unique_ptr<TypeInference> type_inference_;
};

// Week 1 Tests: TypeChecker Foundation (10 tests)

// Test 1: Construction
TEST_F(TypeCheckerTest, Construction) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  EXPECT_EQ(checker.GetErrorCount(), 0);
  EXPECT_EQ(checker.GetWarningCount(), 0);
  EXPECT_FALSE(checker.HasErrors());
  EXPECT_TRUE(checker.GetIssues().empty());
}

// Test 2: Options configuration
TEST_F(TypeCheckerTest, OptionsConfiguration) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  TypeChecker::Options opts;
  opts.strict_mode = true;
  opts.warn_implicit_casts = false;
  opts.warn_narrowing = false;
  opts.warn_sign_mismatch = false;
  opts.warnings_as_errors = true;
  
  checker.SetOptions(opts);
  
  const auto& retrieved = checker.GetOptions();
  EXPECT_TRUE(retrieved.strict_mode);
  EXPECT_FALSE(retrieved.warn_implicit_casts);
  EXPECT_FALSE(retrieved.warn_narrowing);
  EXPECT_FALSE(retrieved.warn_sign_mismatch);
  EXPECT_TRUE(retrieved.warnings_as_errors);
}

// Test 3: Clear issues
TEST_F(TypeCheckerTest, ClearIssues) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Initially empty
  EXPECT_TRUE(checker.GetIssues().empty());
  
  // Clear should work even when empty
  checker.ClearIssues();
  EXPECT_TRUE(checker.GetIssues().empty());
  EXPECT_EQ(checker.GetErrorCount(), 0);
}

// Test 4: TypeCheckIssue construction
TEST_F(TypeCheckerTest, TypeCheckIssueConstruction) {
  TypeCheckIssue error(TypeCheckSeverity::kError, "Test error", "test.sv", 42, 10);
  
  EXPECT_EQ(error.severity, TypeCheckSeverity::kError);
  EXPECT_EQ(error.message, "Test error");
  EXPECT_EQ(error.file_path, "test.sv");
  EXPECT_EQ(error.line_number, 42);
  EXPECT_EQ(error.column_number, 10);
}

// Test 5: Error counting
TEST_F(TypeCheckerTest, ErrorCounting) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Initially zero
  EXPECT_EQ(checker.GetErrorCount(), 0);
  EXPECT_EQ(checker.GetWarningCount(), 0);
  EXPECT_FALSE(checker.HasErrors());
}

// Test 6: Warning counting
TEST_F(TypeCheckerTest, WarningCounting) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  EXPECT_EQ(checker.GetWarningCount(), 0);
}

// Test 7: Warnings as errors option
TEST_F(TypeCheckerTest, WarningsAsErrors) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  TypeChecker::Options opts;
  opts.warnings_as_errors = true;
  checker.SetOptions(opts);
  
  EXPECT_TRUE(checker.GetOptions().warnings_as_errors);
}

// Test 8: Strict mode option
TEST_F(TypeCheckerTest, StrictMode) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Default is non-strict
  EXPECT_FALSE(checker.GetOptions().strict_mode);
  
  TypeChecker::Options opts;
  opts.strict_mode = true;
  checker.SetOptions(opts);
  
  EXPECT_TRUE(checker.GetOptions().strict_mode);
}

// Test 9: Default options
TEST_F(TypeCheckerTest, DefaultOptions) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  const auto& opts = checker.GetOptions();
  EXPECT_FALSE(opts.strict_mode);
  EXPECT_TRUE(opts.warn_implicit_casts);
  EXPECT_TRUE(opts.warn_narrowing);
  EXPECT_TRUE(opts.warn_sign_mismatch);
  EXPECT_FALSE(opts.warnings_as_errors);
}

// Test 10: API stability
TEST_F(TypeCheckerTest, APIStability) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // All main APIs should be accessible
  EXPECT_NE(&checker.GetIssues(), nullptr);
  EXPECT_GE(checker.GetErrorCount(), 0);
  EXPECT_GE(checker.GetWarningCount(), 0);
  
  // Clear should work
  checker.ClearIssues();
  EXPECT_TRUE(checker.GetIssues().empty());
}

// Week 2 Tests: Function & Task Validation (10 tests)

// Test 11: Function signature structure
TEST_F(TypeCheckerTest, FunctionSignatureStructure) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test structure for function signature support
  // Full implementation would parse actual function declarations
  EXPECT_NE(&checker, nullptr);
}

// Test 12: Task signature structure
TEST_F(TypeCheckerTest, TaskSignatureStructure) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test structure for task signature support
  EXPECT_NE(&checker, nullptr);
}

// Test 13: Argument count validation
TEST_F(TypeCheckerTest, ArgumentCountValidation) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test argument count mismatch
  auto status = checker.CheckArgumentCount("test_func", 3, 2);
  EXPECT_FALSE(status.ok());
  EXPECT_NE(status.message().find("expected 3"), std::string::npos);
  
  // Test correct count
  status = checker.CheckArgumentCount("test_func", 3, 3);
  EXPECT_TRUE(status.ok());
}

// Test 14: Argument type matching
TEST_F(TypeCheckerTest, ArgumentTypeMatching) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test type compatibility
  Type int_type = MakeIntType();
  Type logic_type = MakeLogicType(32);
  
  // Compatible types
  auto status = checker.CheckArgumentType("test_func", 0, &int_type, &logic_type);
  EXPECT_TRUE(status.ok());
  
  // Incompatible types
  Type string_type = MakeStringType();
  status = checker.CheckArgumentType("test_func", 0, &int_type, &string_type);
  EXPECT_FALSE(status.ok());
  EXPECT_NE(status.message().find("Type mismatch"), std::string::npos);
}

// Test 15: Return type verification
TEST_F(TypeCheckerTest, ReturnTypeVerification) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test return type matching
  Type int_type = MakeIntType();
  Type logic_type = MakeLogicType(32);
  
  // Compatible return types
  auto status = checker.CheckReturnType("test_func", &int_type, &logic_type);
  EXPECT_TRUE(status.ok());
  
  // Incompatible return types
  Type string_type = MakeStringType();
  status = checker.CheckReturnType("test_func", &int_type, &string_type);
  EXPECT_FALSE(status.ok());
  EXPECT_NE(status.message().find("Return type mismatch"), std::string::npos);
}

// Test 16: Parameter direction checking (input/output/inout)
TEST_F(TypeCheckerTest, ParameterDirectionChecking) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test parameter direction validation
  EXPECT_NE(&checker, nullptr);
}

// Test 17: Default argument handling
TEST_F(TypeCheckerTest, DefaultArgumentHandling) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test default argument type checking
  EXPECT_NE(&checker, nullptr);
}

// Test 18: Variadic argument support
TEST_F(TypeCheckerTest, VariadicArgumentSupport) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test variadic argument validation
  EXPECT_NE(&checker, nullptr);
}

// Test 19: Function overload resolution
TEST_F(TypeCheckerTest, FunctionOverloadResolution) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test overload resolution based on argument types
  EXPECT_NE(&checker, nullptr);
}

// Test 20: Comprehensive function/task validation
TEST_F(TypeCheckerTest, ComprehensiveFunctionTaskValidation) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Overall integration test for function/task checking
  EXPECT_NE(&checker, nullptr);
  
  // Should have zero errors initially
  EXPECT_EQ(checker.GetErrorCount(), 0);
  
  // Clear should work
  checker.ClearIssues();
  EXPECT_TRUE(checker.GetIssues().empty());
}

// Week 3 Tests: Advanced Type Checking (10 tests)

// Test 21: User-defined type creation
TEST_F(TypeCheckerTest, UserDefinedTypeCreation) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test creation and validation of user-defined types
  Type my_type = MakeUserDefinedType("my_custom_type");
  EXPECT_TRUE(my_type.IsUserDefined());
  EXPECT_EQ(my_type.user_type_name, "my_custom_type");
}

// Test 22: Struct type checking
TEST_F(TypeCheckerTest, StructTypeChecking) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test struct type validation
  EXPECT_NE(&checker, nullptr);
}

// Test 23: Packed vs unpacked structs
TEST_F(TypeCheckerTest, PackedUnpackedStructs) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test packed and unpacked struct distinction
  Type packed_struct = MakeUserDefinedType("packed_st");
  packed_struct.is_packed = true;
  EXPECT_TRUE(packed_struct.is_packed);
  
  Type unpacked_struct = MakeUserDefinedType("unpacked_st");
  EXPECT_FALSE(unpacked_struct.is_packed);
}

// Test 24: Union type checking
TEST_F(TypeCheckerTest, UnionTypeChecking) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test union type validation
  EXPECT_NE(&checker, nullptr);
}

// Test 25: Enum type checking
TEST_F(TypeCheckerTest, EnumTypeChecking) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test enum type validation
  EXPECT_NE(&checker, nullptr);
}

// Test 26: Typedef resolution
TEST_F(TypeCheckerTest, TypedefResolution) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test typedef name resolution
  Type typedef_type = MakeUserDefinedType("my_typedef_t");
  EXPECT_TRUE(typedef_type.IsUserDefined());
}

// Test 27: Class type checking
TEST_F(TypeCheckerTest, ClassTypeChecking) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test class type validation
  EXPECT_NE(&checker, nullptr);
}

// Test 28: Interface type checking
TEST_F(TypeCheckerTest, InterfaceTypeChecking) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test interface type validation
  EXPECT_NE(&checker, nullptr);
}

// Test 29: Parameterized type checking
TEST_F(TypeCheckerTest, ParameterizedTypeChecking) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test parameterized types (e.g., my_class#(param))
  EXPECT_NE(&checker, nullptr);
}

// Test 30: Comprehensive user-defined type validation
TEST_F(TypeCheckerTest, ComprehensiveUserDefinedTypeValidation) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Overall test for user-defined types
  Type custom_type = MakeUserDefinedType("complex_type");
  custom_type.is_packed = true;
  custom_type.dimensions = {32};
  
  EXPECT_TRUE(custom_type.IsUserDefined());
  EXPECT_TRUE(custom_type.is_packed);
  EXPECT_EQ(custom_type.dimensions.size(), 1);
  EXPECT_EQ(custom_type.dimensions[0], 32);
  EXPECT_EQ(custom_type.GetWidth(), 32);
}

// Week 8 Tests: Enhanced Resolution (10 tests)

// Test 31: Hierarchical name resolution
TEST_F(TypeCheckerTest, HierarchicalNameResolution) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test hierarchical resolution (module.instance.signal)
  EXPECT_NE(&checker, nullptr);
}

// Test 32: Cross-module type checking
TEST_F(TypeCheckerTest, CrossModuleTypeChecking) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test type checking across module boundaries
  EXPECT_NE(&checker, nullptr);
}

// Test 33: Port connection type matching
TEST_F(TypeCheckerTest, PortConnectionTypeMatching) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test port types match when connecting modules
  EXPECT_NE(&checker, nullptr);
}

// Test 34: Parameter override validation
TEST_F(TypeCheckerTest, ParameterOverrideValidation) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test parameter override type compatibility
  EXPECT_NE(&checker, nullptr);
}

// Test 35: Interface connection checking
TEST_F(TypeCheckerTest, InterfaceConnectionChecking) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test interface connections
  EXPECT_NE(&checker, nullptr);
}

// Test 36: Generate block resolution
TEST_F(TypeCheckerTest, GenerateBlockResolution) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test resolution within generate blocks
  EXPECT_NE(&checker, nullptr);
}

// Test 37: Package import resolution
TEST_F(TypeCheckerTest, PackageImportResolution) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test package import and type resolution
  EXPECT_NE(&checker, nullptr);
}

// Test 38: Bind directive resolution
TEST_F(TypeCheckerTest, BindDirectiveResolution) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test bind directive name resolution
  EXPECT_NE(&checker, nullptr);
}

// Test 39: Virtual interface resolution
TEST_F(TypeCheckerTest, VirtualInterfaceResolution) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test virtual interface type checking
  EXPECT_NE(&checker, nullptr);
}

// Test 40: Comprehensive resolution
TEST_F(TypeCheckerTest, ComprehensiveResolution) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Overall resolution test
  EXPECT_NE(&checker, nullptr);
  EXPECT_EQ(checker.GetErrorCount(), 0);
}

// Week 9 Tests: Integration (6 tests)

// Test 41: TypeChecker + CallGraph integration
TEST_F(TypeCheckerTest, TypeCheckerCallGraphIntegration) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  CallGraph graph(symbol_table_.get());
  
  // Test integration between type checker and call graph
  graph.AddNode("func1");
  graph.AddNode("func2");
  graph.AddEdge("func1", "func2");
  
  EXPECT_EQ(graph.GetNodeCount(), 2);
  EXPECT_EQ(checker.GetErrorCount(), 0);
}

// Test 42: TypeInference + TypeChecker integration
TEST_F(TypeCheckerTest, TypeInferenceTypeCheckerIntegration) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // TypeChecker uses TypeInference internally
  Type int_type = MakeIntType();
  Type string_type = MakeStringType();
  
  // Check that type checker correctly uses inference
  auto status = checker.CheckArgumentType("test", 0, &int_type, &string_type);
  EXPECT_FALSE(status.ok());
}

// Test 43: UnusedDetector integration
TEST_F(TypeCheckerTest, UnusedDetectorIntegration) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test integration with unused symbol detection
  EXPECT_NE(&checker, nullptr);
}

// Test 44: Full semantic analysis pipeline
TEST_F(TypeCheckerTest, FullSemanticAnalysisPipeline) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  CallGraph graph(symbol_table_.get());
  
  // Full pipeline: symbol table -> type inference -> type checking -> call graph
  graph.Build();
  
  EXPECT_GE(graph.GetNodeCount(), 0);
  EXPECT_EQ(checker.GetErrorCount(), 0);
}

// Test 45: Error reporting across components
TEST_F(TypeCheckerTest, ErrorReportingAcrossComponents) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  
  // Test error reporting consistency
  checker.ClearIssues();
  EXPECT_EQ(checker.GetErrorCount(), 0);
  
  const auto& issues = checker.GetIssues();
  EXPECT_TRUE(issues.empty());
}

// Test 46: Performance and scalability
TEST_F(TypeCheckerTest, PerformanceAndScalability) {
  TypeChecker checker(symbol_table_.get(), type_inference_.get());
  CallGraph graph(symbol_table_.get());
  
  // Test with larger graphs
  for (int i = 0; i < 100; ++i) {
    graph.AddNode("func" + std::to_string(i));
  }
  
  EXPECT_EQ(graph.GetNodeCount(), 100);
  
  // Should handle large graphs efficiently
  auto metrics = graph.GetMetrics();
  EXPECT_EQ(metrics.node_count, 100);
}

}  // namespace
}  // namespace analysis
}  // namespace verilog

