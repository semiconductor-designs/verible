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

class VeriPGValidatorCLKIntegrationTest : public ::testing::Test {
 protected:
  // Note: type_checker is created per-test with the actual symbol_table
};

// Test: CLK_001 - Missing clock signal in always_ff
TEST_F(VeriPGValidatorCLKIntegrationTest, DetectMissingClockViolation) {
  const std::string testdata_dir = "verible/verilog/tools/veripg/testdata/clk/";
  const std::string test_file = testdata_dir + "clk_missing_clock_violation.sv";
  
  VerilogProject project(".", std::vector<std::string>{});
  auto file_or = project.OpenTranslationUnit(test_file);
  
  if (!file_or.ok()) {
    GTEST_SKIP() << "Test file not found: " << test_file;
  }
  
  auto* file = file_or.value();
  ASSERT_NE(file, nullptr);
  ASSERT_TRUE(file->Status().ok()) << "Parse failed: " << file->Status().message();
  
  SymbolTable symbol_table(&project);
  std::vector<absl::Status> diagnostics;
  symbol_table.Build(&diagnostics);
  ASSERT_TRUE(diagnostics.empty()) << "Symbol table build had errors";
  
  analysis::TypeInference type_inference(&symbol_table);
  analysis::TypeChecker type_checker(&symbol_table, &type_inference);
  
  VeriPGValidator validator(&type_checker);
  std::vector<Violation> violations;
  
  auto status = validator.CheckClockRules(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  // Should detect CLK_001 violation
  bool found_clk_001 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kCLK_001) {
      found_clk_001 = true;
      EXPECT_EQ(v.severity, Severity::kError);
      EXPECT_THAT(v.message, HasSubstr("clock"));
      EXPECT_THAT(v.message, HasSubstr("always_ff"));
    }
  }
  
  EXPECT_TRUE(found_clk_001) << "Should detect CLK_001 violation for missing clock edge";
}

// Test: CLK_002 - Multiple clocks in single always block
TEST_F(VeriPGValidatorCLKIntegrationTest, DetectMultipleClocksViolation) {
  const std::string testdata_dir = "verible/verilog/tools/veripg/testdata/clk/";
  const std::string test_file = testdata_dir + "clk_multiple_clocks_violation.sv";
  
  VerilogProject project(".", std::vector<std::string>{});
  auto file_or = project.OpenTranslationUnit(test_file);
  
  if (!file_or.ok()) {
    GTEST_SKIP() << "Test file not found: " << test_file;
  }
  
  auto* file = file_or.value();
  ASSERT_NE(file, nullptr);
  ASSERT_TRUE(file->Status().ok()) << "Parse failed: " << file->Status().message();
  
  SymbolTable symbol_table(&project);
  std::vector<absl::Status> diagnostics;
  symbol_table.Build(&diagnostics);
  ASSERT_TRUE(diagnostics.empty()) << "Symbol table build had errors";
  
  analysis::TypeInference type_inference(&symbol_table);
  analysis::TypeChecker type_checker(&symbol_table, &type_inference);
  
  VeriPGValidator validator(&type_checker);
  std::vector<Violation> violations;
  
  auto status = validator.CheckClockRules(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  // Should detect CLK_002 violation
  bool found_clk_002 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kCLK_002) {
      found_clk_002 = true;
      EXPECT_EQ(v.severity, Severity::kError);
      EXPECT_THAT(v.message, HasSubstr("multiple"));
      EXPECT_THAT(v.message, HasSubstr("clock"));
    }
  }
  
  EXPECT_TRUE(found_clk_002) << "Should detect CLK_002 violation for multiple clocks";
}

// Test: CLK_003 - Clock used as data signal
TEST_F(VeriPGValidatorCLKIntegrationTest, DetectClockAsDataViolation) {
  const std::string testdata_dir = "verible/verilog/tools/veripg/testdata/clk/";
  const std::string test_file = testdata_dir + "clk_as_data_violation.sv";
  
  VerilogProject project(".", std::vector<std::string>{});
  auto file_or = project.OpenTranslationUnit(test_file);
  
  if (!file_or.ok()) {
    GTEST_SKIP() << "Test file not found: " << test_file;
  }
  
  auto* file = file_or.value();
  ASSERT_NE(file, nullptr);
  ASSERT_TRUE(file->Status().ok()) << "Parse failed: " << file->Status().message();
  
  SymbolTable symbol_table(&project);
  std::vector<absl::Status> diagnostics;
  symbol_table.Build(&diagnostics);
  ASSERT_TRUE(diagnostics.empty()) << "Symbol table build had errors";
  
  analysis::TypeInference type_inference(&symbol_table);
  analysis::TypeChecker type_checker(&symbol_table, &type_inference);
  
  VeriPGValidator validator(&type_checker);
  std::vector<Violation> violations;
  
  auto status = validator.CheckClockRules(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  // Should detect CLK_003 violation
  bool found_clk_003 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kCLK_003) {
      found_clk_003 = true;
      EXPECT_EQ(v.severity, Severity::kWarning);
      EXPECT_THAT(v.message, HasSubstr("clock"));
      EXPECT_THAT(v.message, HasSubstr("data"));
    }
  }
  
  EXPECT_TRUE(found_clk_003) << "Should detect CLK_003 violation for clock as data";
}

}  // namespace
}  // namespace tools
}  // namespace verilog

