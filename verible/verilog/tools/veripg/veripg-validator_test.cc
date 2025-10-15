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

#include "gtest/gtest.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-checker.h"
#include "verible/verilog/analysis/type-inference.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace tools {
namespace {

class VeriPGValidatorTest : public ::testing::Test {
 protected:
  void SetUp() override {
    project_ = std::make_unique<VerilogProject>(".", std::vector<std::string>{});
    symbol_table_ = std::make_unique<SymbolTable>(project_.get());
    type_inference_ = std::make_unique<analysis::TypeInference>(symbol_table_.get());
    type_checker_ = std::make_unique<analysis::TypeChecker>(symbol_table_.get(), type_inference_.get());
  }

  std::unique_ptr<VerilogProject> project_;
  std::unique_ptr<SymbolTable> symbol_table_;
  std::unique_ptr<analysis::TypeInference> type_inference_;
  std::unique_ptr<analysis::TypeChecker> type_checker_;
};

// Test 1: Constructor
TEST_F(VeriPGValidatorTest, Constructor) {
  VeriPGValidator validator(type_checker_.get());
  EXPECT_TRUE(true);
}

// Test 2: Validate empty symbol table
TEST_F(VeriPGValidatorTest, ValidateEmpty) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  EXPECT_TRUE(result.passed);
  EXPECT_EQ(result.errors_found, 0);
}

// Test 3: Validation result structure
TEST_F(VeriPGValidatorTest, ValidationResultStructure) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  EXPECT_FALSE(result.summary.empty());
  EXPECT_GE(result.errors_found, 0);
  EXPECT_GE(result.warnings_found, 0);
}

// Test 4: Type validation (no type checker)
TEST_F(VeriPGValidatorTest, ValidateTypesWithoutChecker) {
  VeriPGValidator validator(nullptr);
  
  auto status = validator.ValidateTypes(*symbol_table_);
  EXPECT_FALSE(status.ok());
  EXPECT_EQ(status.code(), absl::StatusCode::kFailedPrecondition);
}

// Test 5: Type validation (with type checker)
TEST_F(VeriPGValidatorTest, ValidateTypesWithChecker) {
  VeriPGValidator validator(type_checker_.get());
  
  auto status = validator.ValidateTypes(*symbol_table_);
  EXPECT_TRUE(status.ok());
}

// Test 6: Naming convention validation
TEST_F(VeriPGValidatorTest, ValidateNamingConventions) {
  VeriPGValidator validator(type_checker_.get());
  
  auto status = validator.ValidateNamingConventions(*symbol_table_);
  EXPECT_TRUE(status.ok());
}

// Test 7: Module structure validation
TEST_F(VeriPGValidatorTest, ValidateModuleStructure) {
  VeriPGValidator validator(type_checker_.get());
  
  auto status = validator.ValidateModuleStructure(*symbol_table_);
  EXPECT_TRUE(status.ok());
}

// Test 8: Full validation passed
TEST_F(VeriPGValidatorTest, FullValidationPassed) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  EXPECT_TRUE(result.passed);
  EXPECT_EQ(result.errors_found, 0);
}

// Test 9: Error messages collection
TEST_F(VeriPGValidatorTest, ErrorMessagesCollection) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  // With empty symbol table, should have no errors
  EXPECT_TRUE(result.error_messages.empty());
}

// Test 10: Warning messages collection
TEST_F(VeriPGValidatorTest, WarningMessagesCollection) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  // With empty symbol table, should have no warnings
  EXPECT_TRUE(result.warning_messages.empty());
}

// Test 11: Multiple validations
TEST_F(VeriPGValidatorTest, MultipleValidations) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result1 = validator.Validate(*symbol_table_);
  auto result2 = validator.Validate(*symbol_table_);
  
  EXPECT_EQ(result1.errors_found, result2.errors_found);
  EXPECT_EQ(result1.warnings_found, result2.warnings_found);
}

// Test 12: Summary generation
TEST_F(VeriPGValidatorTest, SummaryGeneration) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  EXPECT_NE(result.summary.find("Validation"), std::string::npos);
  EXPECT_NE(result.summary.find("errors"), std::string::npos);
}

// Test 13: Passed flag consistency
TEST_F(VeriPGValidatorTest, PassedFlagConsistency) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  // passed should be true iff errors_found == 0
  EXPECT_EQ(result.passed, (result.errors_found == 0));
}

// Test 14: Null type checker handling
TEST_F(VeriPGValidatorTest, NullTypeChecker) {
  VeriPGValidator validator(nullptr);
  
  auto result = validator.Validate(*symbol_table_);
  // Should complete but have at least one error
  EXPECT_GT(result.errors_found, 0);
  EXPECT_FALSE(result.passed);
}

// Test 15: Integration with type checker
TEST_F(VeriPGValidatorTest, TypeCheckerIntegration) {
  VeriPGValidator validator(type_checker_.get());
  
  // Validator should successfully integrate with type checker
  auto result = validator.Validate(*symbol_table_);
  EXPECT_TRUE(result.passed);
  EXPECT_FALSE(result.summary.empty());
}

}  // namespace
}  // namespace tools
}  // namespace verilog

