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

class VeriPGValidatorSTRIntegrationTest : public ::testing::Test {
 protected:
  // Structure validation tests
};

// Helper macro for STR tests
#define STR_TEST(test_name, file_name, rule_id, keyword) \
TEST_F(VeriPGValidatorSTRIntegrationTest, test_name) { \
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
  auto status = validator.CheckStructureViolations(symbol_table, violations, &project); \
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

// STR_001: Module has no ports (should be testbench)
STR_TEST(DetectModuleNoPorts,
         "str/str_module_no_ports.sv",
         RuleId::kSTR_001,
         "ports")

// STR_002: Module exceeds complexity threshold
STR_TEST(DetectHighComplexity,
         "str/str_high_complexity.sv",
         RuleId::kSTR_002,
         "complexity")

// STR_003: Deep hierarchy (>5 levels)
STR_TEST(DetectDeepHierarchy,
         "str/str_deep_hierarchy.sv",
         RuleId::kSTR_003,
         "hierarchy")

// STR_004: Missing module header comment
STR_TEST(DetectMissingHeader,
         "str/str_missing_header.sv",
         RuleId::kSTR_004,
         "header")

// STR_005: Wrong port ordering
STR_TEST(DetectWrongPortOrder,
         "str/str_wrong_port_order.sv",
         RuleId::kSTR_005,
         "order")

// STR_006: Instantiation without named ports
STR_TEST(DetectUnnamedPorts,
         "str/str_unnamed_ports.sv",
         RuleId::kSTR_006,
         "named")

// STR_007: Generate block without label
STR_TEST(DetectUnlabeledGenerate,
         "str/str_unlabeled_generate.sv",
         RuleId::kSTR_007,
         "label")

// STR_008: Case statement without default clause
STR_TEST(DetectMissingDefault,
         "str/str_missing_default.sv",
         RuleId::kSTR_008,
         "default")

}  // namespace
}  // namespace tools
}  // namespace verilog
