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

class VeriPGValidatorPWRIntegrationTest : public ::testing::Test {
 protected:
  // Power Intent validation tests
};

// Helper macro to reduce boilerplate
#define PWR_TEST(test_name, file_name, rule_id, keyword) \
TEST_F(VeriPGValidatorPWRIntegrationTest, test_name) { \
  const std::string test_file = \
      "verible/verilog/tools/veripg/testdata/" file_name; \
  \
  VerilogProject project(".", {}); \
  auto file_or = project.OpenTranslationUnit(test_file); \
  if (!file_or.ok()) GTEST_SKIP() << "Test file not found"; \
  \
  auto* file = file_or.value(); \
  ASSERT_NE(file, nullptr); \
  ASSERT_TRUE(file->Status().ok()) << file->Status().message(); \
  \
  SymbolTable symbol_table(&project); \
  std::vector<absl::Status> diagnostics; \
  symbol_table.Build(&diagnostics); \
  ASSERT_TRUE(diagnostics.empty()); \
  \
  analysis::TypeInference type_inference(&symbol_table); \
  analysis::TypeChecker type_checker(&symbol_table, &type_inference); \
  VeriPGValidator validator(&type_checker); \
  std::vector<Violation> violations; \
  \
  auto status = validator.CheckPowerViolations(symbol_table, violations, &project); \
  ASSERT_TRUE(status.ok()) << status.message(); \
  \
  bool found = false; \
  for (const auto& v : violations) { \
    if (v.rule == rule_id) { \
      found = true; \
      EXPECT_EQ(v.severity, Severity::kWarning); \
      EXPECT_THAT(v.message, HasSubstr(keyword)); \
    } \
  } \
  EXPECT_TRUE(found) << "Should detect " #rule_id; \
}

// PWR_001: Missing power domain annotation
PWR_TEST(DetectMissingDomainAnnotation,
         "pwr/pwr_missing_domain_annotation.sv",
         RuleId::kPWR_001,
         "domain")

// PWR_002: Level shifter required at domain boundary
PWR_TEST(DetectMissingLevelShifter,
         "pwr/pwr_missing_level_shifter.sv",
         RuleId::kPWR_002,
         "level")

// PWR_003: Isolation cell required for power-down domain
PWR_TEST(DetectMissingIsolation,
         "pwr/pwr_missing_isolation.sv",
         RuleId::kPWR_003,
         "isolation")

// PWR_004: Retention register without retention annotation
PWR_TEST(DetectMissingRetention,
         "pwr/pwr_missing_retention.sv",
         RuleId::kPWR_004,
         "retention")

// PWR_005: Always-on signal crossing to power-gated domain
PWR_TEST(DetectAlwaysOnCrossing,
         "pwr/pwr_always_on_crossing.sv",
         RuleId::kPWR_005,
         "always-on")

}  // namespace
}  // namespace tools
}  // namespace verilog
