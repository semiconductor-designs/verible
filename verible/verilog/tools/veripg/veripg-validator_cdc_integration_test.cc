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

#include <string>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-checker.h"
#include "verible/verilog/analysis/type-inference.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace tools {
namespace {

using ::testing::HasSubstr;

class VeriPGValidatorCDCIntegrationTest : public ::testing::Test {
 protected:
  // Note: type_checker is created per-test with the actual symbol_table
};

// Test 1: CDC_001 - Detect signal crossing without synchronizer
TEST_F(VeriPGValidatorCDCIntegrationTest, DetectCDCViolationNoSync) {
  // Setup: Create VerilogProject and parse test file
  const std::string testdata_dir = 
      "verible/verilog/tools/veripg/testdata/cdc/";
  const std::string test_file = testdata_dir + "cdc_violation_no_sync.sv";
  
  VerilogProject project(".", std::vector<std::string>{});
  auto file_or = project.OpenTranslationUnit(test_file);
  
  // Skip test if file doesn't exist (CI environment may not have testdata)
  if (!file_or.ok()) {
    GTEST_SKIP() << "Test file not found: " << test_file;
  }
  
  auto* file = file_or.value();
  ASSERT_NE(file, nullptr);
  ASSERT_TRUE(file->Status().ok()) << "Parse failed: " << file->Status().message();
  
  // Build symbol table
  SymbolTable symbol_table(&project);
  std::vector<absl::Status> diagnostics;
  symbol_table.Build(&diagnostics);
  ASSERT_TRUE(diagnostics.empty()) << "Symbol table build had errors";
  
  // Create type inference and checker
  analysis::TypeInference type_inference(&symbol_table);
  analysis::TypeChecker type_checker(&symbol_table, &type_inference);
  
  // Test: Check for CDC violations
  VeriPGValidator validator(&type_checker);
  std::vector<Violation> violations;
  
  auto status = validator.CheckCDCViolations(symbol_table, violations, &project);
  EXPECT_TRUE(status.ok());
  
  // Assert: Should detect CDC_001 violation
  ASSERT_GT(violations.size(), 0) << "Should detect at least one CDC violation";
  
  bool found_cdc_001 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kCDC_001) {
      found_cdc_001 = true;
      EXPECT_EQ(v.severity, Severity::kError);
      EXPECT_THAT(v.message, HasSubstr("clock domain"));
      EXPECT_THAT(v.message, HasSubstr("clk_a"));
      EXPECT_THAT(v.message, HasSubstr("clk_b"));
      EXPECT_THAT(v.signal_name, HasSubstr("data_a"));
      EXPECT_THAT(v.fix_suggestion, HasSubstr("synchronizer"));
    }
  }
  
  EXPECT_TRUE(found_cdc_001) << "Should detect CDC_001 violation for data_a";
}

// Test 2: Valid CDC - No violation when synchronizer is present
TEST_F(VeriPGValidatorCDCIntegrationTest, ValidCDCWithSynchronizer) {
  const std::string testdata_dir = 
      "verible/verilog/tools/veripg/testdata/cdc/";
  const std::string test_file = testdata_dir + "cdc_valid_with_sync.sv";
  
  VerilogProject project(".", std::vector<std::string>{});
  auto file_or = project.OpenTranslationUnit(test_file);
  
  if (!file_or.ok()) {
    GTEST_SKIP() << "Test file not found: " << test_file;
  }
  
  auto* file = file_or.value();
  ASSERT_NE(file, nullptr);
  ASSERT_TRUE(file->Status().ok());
  
  SymbolTable symbol_table(&project);
  std::vector<absl::Status> diagnostics;
  symbol_table.Build(&diagnostics);
  ASSERT_TRUE(diagnostics.empty());
  
  // Create type inference and checker
  analysis::TypeInference type_inference(&symbol_table);
  analysis::TypeChecker type_checker(&symbol_table, &type_inference);
  
  // Test: Check for CDC violations
  VeriPGValidator validator(&type_checker);
  std::vector<Violation> violations;
  
  auto status = validator.CheckCDCViolations(symbol_table, violations, &project);
  EXPECT_TRUE(status.ok());
  
  // Assert: Should NOT detect any CDC violations (sync is present)
  EXPECT_EQ(violations.size(), 0) 
      << "Should not detect CDC violation when proper synchronizer exists";
}

// Test 3: Same domain - No violation when signals in same clock domain
TEST_F(VeriPGValidatorCDCIntegrationTest, SameDomainNoCDC) {
  const std::string testdata_dir = 
      "verible/verilog/tools/veripg/testdata/cdc/";
  const std::string test_file = testdata_dir + "cdc_same_domain.sv";
  
  VerilogProject project(".", std::vector<std::string>{});
  auto file_or = project.OpenTranslationUnit(test_file);
  
  if (!file_or.ok()) {
    GTEST_SKIP() << "Test file not found: " << test_file;
  }
  
  auto* file = file_or.value();
  ASSERT_NE(file, nullptr);
  ASSERT_TRUE(file->Status().ok());
  
  SymbolTable symbol_table(&project);
  std::vector<absl::Status> diagnostics;
  symbol_table.Build(&diagnostics);
  ASSERT_TRUE(diagnostics.empty());
  
  // Create type inference and checker
  analysis::TypeInference type_inference(&symbol_table);
  analysis::TypeChecker type_checker(&symbol_table, &type_inference);
  
  // Test: Check for CDC violations
  VeriPGValidator validator(&type_checker);
  std::vector<Violation> violations;
  
  auto status = validator.CheckCDCViolations(symbol_table, violations, &project);
  EXPECT_TRUE(status.ok());
  
  // Assert: Should NOT detect any CDC violations (same domain)
  EXPECT_EQ(violations.size(), 0) 
      << "Should not detect CDC violation when signals in same clock domain";
}

// Test 4: Multiple violations - Detect multiple CDC issues in one module
TEST_F(VeriPGValidatorCDCIntegrationTest, MultipleViolations) {
  const std::string testdata_dir = 
      "verible/verilog/tools/veripg/testdata/cdc/";
  const std::string test_file = testdata_dir + "cdc_multiple_violations.sv";
  
  VerilogProject project(".", std::vector<std::string>{});
  auto file_or = project.OpenTranslationUnit(test_file);
  
  if (!file_or.ok()) {
    GTEST_SKIP() << "Test file not found: " << test_file;
  }
  
  auto* file = file_or.value();
  ASSERT_NE(file, nullptr);
  ASSERT_TRUE(file->Status().ok());
  
  SymbolTable symbol_table(&project);
  std::vector<absl::Status> diagnostics;
  symbol_table.Build(&diagnostics);
  ASSERT_TRUE(diagnostics.empty());
  
  // Create type inference and checker
  analysis::TypeInference type_inference(&symbol_table);
  analysis::TypeChecker type_checker(&symbol_table, &type_inference);
  
  // Test: Check for CDC violations
  VeriPGValidator validator(&type_checker);
  std::vector<Violation> violations;
  
  auto status = validator.CheckCDCViolations(symbol_table, violations, &project);
  EXPECT_TRUE(status.ok());
  
  // Assert: Should detect 2 CDC violations
  EXPECT_GE(violations.size(), 2) 
      << "Should detect at least 2 CDC violations (sig_a1 and sig_a2)";
  
  // Verify both violations are CDC_001
  int cdc_001_count = 0;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kCDC_001) {
      cdc_001_count++;
      EXPECT_EQ(v.severity, Severity::kError);
      EXPECT_THAT(v.message, HasSubstr("clock domain"));
    }
  }
  
  EXPECT_GE(cdc_001_count, 2) << "Should detect at least 2 CDC_001 violations";
}

}  // namespace
}  // namespace tools
}  // namespace verilog

