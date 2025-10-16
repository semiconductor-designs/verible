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
  // Framework tests for Structure rules
};

// Test: STR rules framework
TEST_F(VeriPGValidatorSTRIntegrationTest, DetectStructureViolationsFramework) {
  const std::string testdata_dir = "verible/verilog/tools/veripg/testdata/str/";
  const std::string test_file = testdata_dir + "str_no_ports_violation.sv";
  
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
  
  auto status = validator.CheckStructureViolations(symbol_table, violations);
  ASSERT_TRUE(status.ok()) << status.message();
  
  // Framework test: verify violations are generated
  EXPECT_GE(violations.size(), 1) << "Should generate sample violations";
  
  // Check for STR rule violations
  bool found_str = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kSTR_001 || v.rule == RuleId::kSTR_005 || v.rule == RuleId::kSTR_008) {
      found_str = true;
      EXPECT_EQ(v.severity, Severity::kWarning);
    }
  }
  EXPECT_TRUE(found_str) << "Should detect STR violations";
}

}  // namespace
}  // namespace tools
}  // namespace verilog

