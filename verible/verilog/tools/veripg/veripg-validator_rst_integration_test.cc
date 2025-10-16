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

class VeriPGValidatorRSTIntegrationTest : public ::testing::Test {
 protected:
  // Note: type_checker is created per-test with the actual symbol_table
};

// Test: RST_001 - Missing reset in sequential logic
TEST_F(VeriPGValidatorRSTIntegrationTest, DetectMissingResetViolation) {
  const std::string testdata_dir = "verible/verilog/tools/veripg/testdata/rst/";
  const std::string test_file = testdata_dir + "rst_missing_reset_violation.sv";
  
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
  
  auto status = validator.CheckResetRules(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  // Should detect RST_001 violation
  bool found_rst_001 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kRST_001) {
      found_rst_001 = true;
      EXPECT_EQ(v.severity, Severity::kWarning);
      EXPECT_THAT(v.message, HasSubstr("reset"));
      EXPECT_THAT(v.message, HasSubstr("always_ff"));
    }
  }
  
  EXPECT_TRUE(found_rst_001) << "Should detect RST_001 violation for missing reset";
}

}  // namespace
}  // namespace tools
}  // namespace verilog

