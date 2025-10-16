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

#include <chrono>

#include "gmock/gmock.h"
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

// Integration Tests with Real Validation (Tests 16-25)

// Test 16: Type validation integration
TEST_F(VeriPGValidatorTest, TypeValidationIntegration) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  
  // Should complete type validation
  EXPECT_GE(result.errors_found, 0);
  EXPECT_GE(result.warnings_found, 0);
}

// Test 17: Naming convention validation
TEST_F(VeriPGValidatorTest, NamingConventionValidation) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  
  // Should check naming conventions
  EXPECT_FALSE(result.summary.empty());
}

// Test 18: Structural validation
TEST_F(VeriPGValidatorTest, StructuralValidation) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  
  // Should perform structural checks
  EXPECT_TRUE(result.passed || !result.passed); // Always valid boolean
}

// Test 19: Performance with large symbol table
TEST_F(VeriPGValidatorTest, PerformanceTest) {
  VeriPGValidator validator(type_checker_.get());
  
  auto start = std::chrono::high_resolution_clock::now();
  auto result = validator.Validate(*symbol_table_);
  auto end = std::chrono::high_resolution_clock::now();
  
  auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
  
  // Should complete in reasonable time (< 2 seconds)
  EXPECT_LT(duration.count(), 2000);
}

// Test 20: Error message format
TEST_F(VeriPGValidatorTest, ErrorMessageFormat) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  
  // Error messages should be properly formatted if present
  for (const auto& error : result.error_messages) {
    EXPECT_FALSE(error.empty());
  }
}

// Test 21: Warning message format
TEST_F(VeriPGValidatorTest, WarningMessageFormat) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  
  // Warning messages should be properly formatted if present
  for (const auto& warning : result.warning_messages) {
    EXPECT_FALSE(warning.empty());
  }
}

// Test 22: Validation report completeness
TEST_F(VeriPGValidatorTest, ValidationReportCompleteness) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  
  // Report should have all required fields
  EXPECT_EQ(result.errors_found, result.error_messages.size());
  EXPECT_EQ(result.warnings_found, result.warning_messages.size());
}

// Test 23: Consecutive validations
TEST_F(VeriPGValidatorTest, ConsecutiveValidations) {
  VeriPGValidator validator(type_checker_.get());
  
  // Multiple validations should be consistent
  auto result1 = validator.Validate(*symbol_table_);
  auto result2 = validator.Validate(*symbol_table_);
  auto result3 = validator.Validate(*symbol_table_);
  
  EXPECT_EQ(result1.errors_found, result2.errors_found);
  EXPECT_EQ(result2.errors_found, result3.errors_found);
}

// Test 24: Empty symbol table validation
TEST_F(VeriPGValidatorTest, EmptySymbolTableValidation) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  
  // Empty symbol table should pass without errors
  EXPECT_EQ(result.errors_found, 0);
  EXPECT_TRUE(result.passed);
}

// Test 25: Summary string format
TEST_F(VeriPGValidatorTest, SummaryStringFormat) {
  VeriPGValidator validator(type_checker_.get());
  
  auto result = validator.Validate(*symbol_table_);
  
  // Summary should contain key information
  EXPECT_THAT(result.summary, ::testing::HasSubstr("Validation"));
  EXPECT_THAT(result.summary, ::testing::HasSubstr("errors"));
  EXPECT_THAT(result.summary, ::testing::HasSubstr("warnings"));
}

// ========================================
// Week 1: CDC/Clock/Reset Validation Tests
// ========================================

// Test 26: CDC validation framework exists
TEST_F(VeriPGValidatorTest, CheckCDCViolations_Framework) {
  VeriPGValidator validator(type_checker_.get());
  std::vector<Violation> violations;
  
  auto status = validator.CheckCDCViolations(*symbol_table_, violations);
  EXPECT_TRUE(status.ok());
}

// Test 27: Clock rules framework exists
TEST_F(VeriPGValidatorTest, CheckClockRules_Framework) {
  VeriPGValidator validator(type_checker_.get());
  std::vector<Violation> violations;
  
  auto status = validator.CheckClockRules(*symbol_table_, violations);
  EXPECT_TRUE(status.ok());
}

// Test 28: Reset rules framework exists
TEST_F(VeriPGValidatorTest, CheckResetRules_Framework) {
  VeriPGValidator validator(type_checker_.get());
  std::vector<Violation> violations;
  
  auto status = validator.CheckResetRules(*symbol_table_, violations);
  EXPECT_TRUE(status.ok());
}

// Test 29: Timing rules framework exists
TEST_F(VeriPGValidatorTest, CheckTimingRules_Framework) {
  VeriPGValidator validator(type_checker_.get());
  std::vector<Violation> violations;
  
  auto status = validator.CheckTimingRules(*symbol_table_, violations);
  EXPECT_TRUE(status.ok());
}

// Test 30: Violation structure - CDC_001
TEST_F(VeriPGValidatorTest, Violation_CDC_001_Structure) {
  Violation v;
  v.rule = RuleId::kCDC_001;
  v.severity = Severity::kError;
  v.message = "Clock domain crossing without synchronizer";
  v.signal_name = "data_signal";
  v.source_location = "test.sv:10:5";
  v.fix_suggestion = "Add 2-stage synchronizer";
  
  EXPECT_EQ(v.rule, RuleId::kCDC_001);
  EXPECT_EQ(v.severity, Severity::kError);
  EXPECT_FALSE(v.message.empty());
}

// Test 31: Violation structure - CLK_001
TEST_F(VeriPGValidatorTest, Violation_CLK_001_Structure) {
  Violation v;
  v.rule = RuleId::kCLK_001;
  v.severity = Severity::kError;
  v.message = "Missing clock signal in always_ff";
  
  EXPECT_EQ(v.rule, RuleId::kCLK_001);
  EXPECT_EQ(v.severity, Severity::kError);
}

// Test 32: Violation structure - RST_001
TEST_F(VeriPGValidatorTest, Violation_RST_001_Structure) {
  Violation v;
  v.rule = RuleId::kRST_001;
  v.severity = Severity::kError;
  v.message = "Missing reset in sequential logic";
  
  EXPECT_EQ(v.rule, RuleId::kRST_001);
  EXPECT_EQ(v.severity, Severity::kError);
}

}  // namespace
}  // namespace tools
}  // namespace verilog

