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

class VeriPGValidatorTIMIntegrationTest : public ::testing::Test {
 protected:
  // Note: type_checker is created per-test with the actual symbol_table
};

// Test: TIM_001 - Combinational loop detected
TEST_F(VeriPGValidatorTIMIntegrationTest, DetectCombLoopViolation) {
  const std::string testdata_dir = "verible/verilog/tools/veripg/testdata/tim/";
  const std::string test_file = testdata_dir + "tim_comb_loop_violation.sv";
  
  VerilogProject project(".", std::vector<std::string>{});
  auto file_or = project.OpenTranslationUnit(test_file);
  if (!file_or.ok()) GTEST_SKIP() << "Test file not found";
  
  auto* file = file_or.value();
  ASSERT_NE(file, nullptr);
  ASSERT_TRUE(file->Status().ok()) << file->Status().message();
  
  SymbolTable symbol_table(&project);
  std::vector<absl::Status> diagnostics;
  symbol_table.Build(&diagnostics);
  ASSERT_TRUE(diagnostics.empty());
  
  analysis::TypeInference type_inference(&symbol_table);
  analysis::TypeChecker type_checker(&symbol_table, &type_inference);
  VeriPGValidator validator(&type_checker);
  std::vector<Violation> violations;
  
  auto status = validator.CheckTimingRules(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  bool found_tim_001 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kTIM_001) {
      found_tim_001 = true;
      EXPECT_EQ(v.severity, Severity::kError);
      EXPECT_THAT(v.message, HasSubstr("loop"));
    }
  }
  EXPECT_TRUE(found_tim_001) << "Should detect TIM_001 for combinational loop";
}

// Test: TIM_002 - Latch inferred
TEST_F(VeriPGValidatorTIMIntegrationTest, DetectLatchInferredViolation) {
  const std::string testdata_dir = "verible/verilog/tools/veripg/testdata/tim/";
  const std::string test_file = testdata_dir + "tim_latch_inferred_violation.sv";
  
  VerilogProject project(".", std::vector<std::string>{});
  auto file_or = project.OpenTranslationUnit(test_file);
  if (!file_or.ok()) GTEST_SKIP() << "Test file not found";
  
  auto* file = file_or.value();
  ASSERT_NE(file, nullptr);
  ASSERT_TRUE(file->Status().ok()) << file->Status().message();
  
  SymbolTable symbol_table(&project);
  std::vector<absl::Status> diagnostics;
  symbol_table.Build(&diagnostics);
  ASSERT_TRUE(diagnostics.empty());
  
  analysis::TypeInference type_inference(&symbol_table);
  analysis::TypeChecker type_checker(&symbol_table, &type_inference);
  VeriPGValidator validator(&type_checker);
  std::vector<Violation> violations;
  
  auto status = validator.CheckTimingRules(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  bool found_tim_002 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kTIM_002) {
      found_tim_002 = true;
      EXPECT_EQ(v.severity, Severity::kWarning);
      EXPECT_THAT(v.message, HasSubstr("latch"));
    }
  }
  EXPECT_TRUE(found_tim_002) << "Should detect TIM_002 for latch inference";
}

}  // namespace
}  // namespace tools
}  // namespace verilog

