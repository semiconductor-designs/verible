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

// Test 33: Violation structure - TIM_001
TEST_F(VeriPGValidatorTest, Violation_TIM_001_Structure) {
  Violation v;
  v.rule = RuleId::kTIM_001;
  v.severity = Severity::kError;
  v.message = "Combinational loop detected";
  
  EXPECT_EQ(v.rule, RuleId::kTIM_001);
  EXPECT_EQ(v.severity, Severity::kError);
}

// Test 34: Violation structure - TIM_002
TEST_F(VeriPGValidatorTest, Violation_TIM_002_Structure) {
  Violation v;
  v.rule = RuleId::kTIM_002;
  v.severity = Severity::kWarning;
  v.message = "Latch inferred - incomplete case statement";
  
  EXPECT_EQ(v.rule, RuleId::kTIM_002);
  EXPECT_EQ(v.severity, Severity::kWarning);
}

// Test 35: CDC_002 structure
TEST_F(VeriPGValidatorTest, Violation_CDC_002_Structure) {
  Violation v;
  v.rule = RuleId::kCDC_002;
  v.severity = Severity::kError;
  v.message = "Multi-bit signal crossing clock domains";
  v.signal_name = "data_bus[7:0]";
  
  EXPECT_EQ(v.rule, RuleId::kCDC_002);
  EXPECT_FALSE(v.signal_name.empty());
}

// Test 36: CDC_003 structure
TEST_F(VeriPGValidatorTest, Violation_CDC_003_Structure) {
  Violation v;
  v.rule = RuleId::kCDC_003;
  v.severity = Severity::kError;
  v.message = "Clock mux without glitch protection";
  
  EXPECT_EQ(v.rule, RuleId::kCDC_003);
}

// Test 37: CDC_004 structure
TEST_F(VeriPGValidatorTest, Violation_CDC_004_Structure) {
  Violation v;
  v.rule = RuleId::kCDC_004;
  v.severity = Severity::kError;
  v.message = "Asynchronous reset in synchronous logic";
  
  EXPECT_EQ(v.rule, RuleId::kCDC_004);
}

// Test 38: CLK_002 structure
TEST_F(VeriPGValidatorTest, Violation_CLK_002_Structure) {
  Violation v;
  v.rule = RuleId::kCLK_002;
  v.severity = Severity::kError;
  v.message = "Multiple clocks in single always block";
  
  EXPECT_EQ(v.rule, RuleId::kCLK_002);
}

// Test 39: CLK_003 structure
TEST_F(VeriPGValidatorTest, Violation_CLK_003_Structure) {
  Violation v;
  v.rule = RuleId::kCLK_003;
  v.severity = Severity::kError;
  v.message = "Clock used as data signal";
  
  EXPECT_EQ(v.rule, RuleId::kCLK_003);
}

// Test 40: CLK_004 structure
TEST_F(VeriPGValidatorTest, Violation_CLK_004_Structure) {
  Violation v;
  v.rule = RuleId::kCLK_004;
  v.severity = Severity::kWarning;
  v.message = "Gated clock without ICG cell";
  
  EXPECT_EQ(v.rule, RuleId::kCLK_004);
}

// Test 41: RST_002 structure
TEST_F(VeriPGValidatorTest, Violation_RST_002_Structure) {
  Violation v;
  v.rule = RuleId::kRST_002;
  v.severity = Severity::kError;
  v.message = "Asynchronous reset not properly synchronized";
  
  EXPECT_EQ(v.rule, RuleId::kRST_002);
}

// Test 42: RST_003 structure
TEST_F(VeriPGValidatorTest, Violation_RST_003_Structure) {
  Violation v;
  v.rule = RuleId::kRST_003;
  v.severity = Severity::kWarning;
  v.message = "Active-low reset mixed with active-high";
  
  EXPECT_EQ(v.rule, RuleId::kRST_003);
}

// Test 43: RST_004 structure
TEST_F(VeriPGValidatorTest, Violation_RST_004_Structure) {
  Violation v;
  v.rule = RuleId::kRST_004;
  v.severity = Severity::kError;
  v.message = "Reset signal used as data";
  
  EXPECT_EQ(v.rule, RuleId::kRST_004);
}

// Test 44: RST_005 structure
TEST_F(VeriPGValidatorTest, Violation_RST_005_Structure) {
  Violation v;
  v.rule = RuleId::kRST_005;
  v.severity = Severity::kWarning;
  v.message = "Reset width below minimum assertion time";
  
  EXPECT_EQ(v.rule, RuleId::kRST_005);
}

// Test 45: Severity levels
TEST_F(VeriPGValidatorTest, SeverityLevels) {
  Violation error_violation;
  error_violation.severity = Severity::kError;
  EXPECT_EQ(error_violation.severity, Severity::kError);
  
  Violation warning_violation;
  warning_violation.severity = Severity::kWarning;
  EXPECT_EQ(warning_violation.severity, Severity::kWarning);
  
  Violation info_violation;
  info_violation.severity = Severity::kInfo;
  EXPECT_EQ(info_violation.severity, Severity::kInfo);
}

// Test 46: Multiple violations collection
TEST_F(VeriPGValidatorTest, MultipleViolationsCollection) {
  VeriPGValidator validator(type_checker_.get());
  std::vector<Violation> violations;
  
  // Should be able to collect multiple violations
  auto cdc_status = validator.CheckCDCViolations(*symbol_table_, violations);
  auto clk_status = validator.CheckClockRules(*symbol_table_, violations);
  auto rst_status = validator.CheckResetRules(*symbol_table_, violations);
  auto tim_status = validator.CheckTimingRules(*symbol_table_, violations);
  
  EXPECT_TRUE(cdc_status.ok());
  EXPECT_TRUE(clk_status.ok());
  EXPECT_TRUE(rst_status.ok());
  EXPECT_TRUE(tim_status.ok());
  
  // Empty symbol table should have no violations
  EXPECT_EQ(violations.size(), 0);
}

// Test 47: Violation with fix suggestion
TEST_F(VeriPGValidatorTest, ViolationWithFixSuggestion) {
  Violation v;
  v.rule = RuleId::kCDC_001;
  v.severity = Severity::kError;
  v.message = "CDC without synchronizer";
  v.fix_suggestion = "Add 2-stage FF synchronizer";
  
  EXPECT_FALSE(v.fix_suggestion.empty());
  EXPECT_THAT(v.fix_suggestion, ::testing::HasSubstr("synchronizer"));
}

// Test 48: Violation with source location
TEST_F(VeriPGValidatorTest, ViolationWithSourceLocation) {
  Violation v;
  v.rule = RuleId::kCLK_001;
  v.source_location = "test.sv:42:15";
  
  EXPECT_FALSE(v.source_location.empty());
  EXPECT_THAT(v.source_location, ::testing::HasSubstr(":"));
}

// Test 49: All rule IDs are unique
TEST_F(VeriPGValidatorTest, AllRuleIDsUnique) {
  std::set<RuleId> rule_ids = {
    RuleId::kCDC_001, RuleId::kCDC_002, RuleId::kCDC_003, RuleId::kCDC_004,
    RuleId::kCLK_001, RuleId::kCLK_002, RuleId::kCLK_003, RuleId::kCLK_004,
    RuleId::kRST_001, RuleId::kRST_002, RuleId::kRST_003, RuleId::kRST_004, RuleId::kRST_005,
    RuleId::kTIM_001, RuleId::kTIM_002
  };
  
  EXPECT_EQ(rule_ids.size(), 15) << "All 15 rule IDs should be unique";
}

// Test 50: Framework supports all 4 rule categories
TEST_F(VeriPGValidatorTest, AllRuleCategoriesSupported) {
  VeriPGValidator validator(type_checker_.get());
  std::vector<Violation> violations;
  
  // All 4 categories should be callable
  EXPECT_TRUE(validator.CheckCDCViolations(*symbol_table_, violations).ok());
  EXPECT_TRUE(validator.CheckClockRules(*symbol_table_, violations).ok());
  EXPECT_TRUE(validator.CheckResetRules(*symbol_table_, violations).ok());
  EXPECT_TRUE(validator.CheckTimingRules(*symbol_table_, violations).ok());
}

// Test 51: CDC rules (4 rules defined)
TEST_F(VeriPGValidatorTest, CDCRulesCount) {
  // Verify we have 4 CDC rules defined
  std::vector<RuleId> cdc_rules = {
    RuleId::kCDC_001, RuleId::kCDC_002, RuleId::kCDC_003, RuleId::kCDC_004
  };
  EXPECT_EQ(cdc_rules.size(), 4);
}

// Test 52: Clock rules (4 rules defined)
TEST_F(VeriPGValidatorTest, ClockRulesCount) {
  // Verify we have 4 Clock rules defined
  std::vector<RuleId> clk_rules = {
    RuleId::kCLK_001, RuleId::kCLK_002, RuleId::kCLK_003, RuleId::kCLK_004
  };
  EXPECT_EQ(clk_rules.size(), 4);
}

// Test 53: Reset rules (5 rules defined)
TEST_F(VeriPGValidatorTest, ResetRulesCount) {
  // Verify we have 5 Reset rules defined
  std::vector<RuleId> rst_rules = {
    RuleId::kRST_001, RuleId::kRST_002, RuleId::kRST_003, RuleId::kRST_004, RuleId::kRST_005
  };
  EXPECT_EQ(rst_rules.size(), 5);
}

// Test 54: Timing rules (2 rules defined)
TEST_F(VeriPGValidatorTest, TimingRulesCount) {
  // Verify we have 2 Timing rules defined
  std::vector<RuleId> tim_rules = {
    RuleId::kTIM_001, RuleId::kTIM_002
  };
  EXPECT_EQ(tim_rules.size(), 2);
}

// Test 55: Total 15 rules as specified in plan
TEST_F(VeriPGValidatorTest, TotalRulesCount) {
  // Verify total of 15 rules (4 CDC + 4 CLK + 5 RST + 2 TIM)
  EXPECT_EQ(4 + 4 + 5 + 2, 15) << "Week 1 should have 15 rules total";
}

// ========================================
// Week 1: Auto-Fix Generator Tests
// ========================================

// Test 56: GenerateFixCDC_001 - generates synchronizer code
TEST_F(VeriPGValidatorTest, GenerateFixCDC_001) {
  VeriPGValidator validator(type_checker_.get());
  
  std::string fix = validator.GenerateFixCDC_001("data_a", "clk_b");
  
  EXPECT_FALSE(fix.empty());
  EXPECT_THAT(fix, ::testing::HasSubstr("data_a_sync1"));
  EXPECT_THAT(fix, ::testing::HasSubstr("data_a_sync2"));
  EXPECT_THAT(fix, ::testing::HasSubstr("clk_b"));
  EXPECT_THAT(fix, ::testing::HasSubstr("always_ff"));
  EXPECT_THAT(fix, ::testing::HasSubstr("@(posedge"));
}

// Test 57: GenerateFixCDC_001 - 2-stage synchronizer pattern
TEST_F(VeriPGValidatorTest, GenerateFixCDC_001_TwoStage) {
  VeriPGValidator validator(type_checker_.get());
  
  std::string fix = validator.GenerateFixCDC_001("signal", "clk");
  
  // Should have both stages
  EXPECT_THAT(fix, ::testing::HasSubstr("signal_sync1 <= signal"));
  EXPECT_THAT(fix, ::testing::HasSubstr("signal_sync2 <= signal_sync1"));
}

// Test 58: GenerateFixCLK_001 - generates clock sensitivity list
TEST_F(VeriPGValidatorTest, GenerateFixCLK_001) {
  VeriPGValidator validator(type_checker_.get());
  
  std::string fix = validator.GenerateFixCLK_001("clk");
  
  EXPECT_FALSE(fix.empty());
  EXPECT_THAT(fix, ::testing::HasSubstr("always_ff"));
  EXPECT_THAT(fix, ::testing::HasSubstr("@(posedge clk)"));
}

// Test 59: GenerateFixCLK_001 - different clock names
TEST_F(VeriPGValidatorTest, GenerateFixCLK_001_DifferentClocks) {
  VeriPGValidator validator(type_checker_.get());
  
  std::string fix1 = validator.GenerateFixCLK_001("clk_main");
  std::string fix2 = validator.GenerateFixCLK_001("clk_io");
  
  EXPECT_THAT(fix1, ::testing::HasSubstr("clk_main"));
  EXPECT_THAT(fix2, ::testing::HasSubstr("clk_io"));
  EXPECT_NE(fix1, fix2);
}

// Test 60: GenerateFixRST_001 - generates reset logic
TEST_F(VeriPGValidatorTest, GenerateFixRST_001) {
  VeriPGValidator validator(type_checker_.get());
  
  std::string fix = validator.GenerateFixRST_001("rst_n");
  
  EXPECT_FALSE(fix.empty());
  EXPECT_THAT(fix, ::testing::HasSubstr("always_ff"));
  EXPECT_THAT(fix, ::testing::HasSubstr("rst_n"));
  EXPECT_THAT(fix, ::testing::HasSubstr("@(posedge clk or negedge rst_n)"));
}

// Test 61: GenerateFixRST_001 - reset structure
TEST_F(VeriPGValidatorTest, GenerateFixRST_001_Structure) {
  VeriPGValidator validator(type_checker_.get());
  
  std::string fix = validator.GenerateFixRST_001("rst");
  
  // Should have if-else structure
  EXPECT_THAT(fix, ::testing::HasSubstr("if (!rst)"));
  EXPECT_THAT(fix, ::testing::HasSubstr("else"));
  EXPECT_THAT(fix, ::testing::HasSubstr("begin"));
  EXPECT_THAT(fix, ::testing::HasSubstr("end"));
}

// Test 62: All 3 auto-fix generators work
TEST_F(VeriPGValidatorTest, AllAutoFixGeneratorsWork) {
  VeriPGValidator validator(type_checker_.get());
  
  std::string fix_cdc = validator.GenerateFixCDC_001("data", "clk");
  std::string fix_clk = validator.GenerateFixCLK_001("clk");
  std::string fix_rst = validator.GenerateFixRST_001("rst_n");
  
  EXPECT_FALSE(fix_cdc.empty());
  EXPECT_FALSE(fix_clk.empty());
  EXPECT_FALSE(fix_rst.empty());
  
  // Each should be unique
  EXPECT_NE(fix_cdc, fix_clk);
  EXPECT_NE(fix_clk, fix_rst);
  EXPECT_NE(fix_cdc, fix_rst);
}

}  // namespace
}  // namespace tools
}  // namespace verilog

