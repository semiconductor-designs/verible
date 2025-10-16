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

class VeriPGValidatorNAMIntegrationTest : public ::testing::Test {
 protected:
  // Note: type_checker is created per-test with the actual symbol_table
};

// Test: NAM_001 - Module naming convention
TEST_F(VeriPGValidatorNAMIntegrationTest, DetectModuleNamingViolation) {
  const std::string testdata_dir = "verible/verilog/tools/veripg/testdata/nam/";
  const std::string test_file = testdata_dir + "nam_module_naming_violation.sv";
  
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
  
  auto status = validator.CheckNamingViolations(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  bool found_nam_001 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kNAM_001) {
      found_nam_001 = true;
      EXPECT_EQ(v.severity, Severity::kWarning);
      EXPECT_THAT(v.message, HasSubstr("lowercase"));
    }
  }
  EXPECT_TRUE(found_nam_001) << "Should detect NAM_001 for module naming";
}

// Test: NAM_002 - Signal names too short
TEST_F(VeriPGValidatorNAMIntegrationTest, DetectShortSignalNameViolation) {
  const std::string testdata_dir = "verible/verilog/tools/veripg/testdata/nam/";
  const std::string test_file = testdata_dir + "nam_signal_short_violation.sv";
  
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
  
  auto status = validator.CheckNamingViolations(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  bool found_nam_002 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kNAM_002) {
      found_nam_002 = true;
      EXPECT_EQ(v.severity, Severity::kWarning);
      EXPECT_THAT(v.message, HasSubstr("short"));
    }
  }
  EXPECT_TRUE(found_nam_002) << "Should detect NAM_002 for short signal names";
}

// Test: NAM_003 - Parameter naming
TEST_F(VeriPGValidatorNAMIntegrationTest, DetectParameterNamingViolation) {
  const std::string testdata_dir = "verible/verilog/tools/veripg/testdata/nam/";
  const std::string test_file = testdata_dir + "nam_parameter_naming_violation.sv";
  
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
  
  auto status = validator.CheckNamingViolations(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  bool found_nam_003 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kNAM_003) {
      found_nam_003 = true;
      EXPECT_EQ(v.severity, Severity::kWarning);
      EXPECT_THAT(v.message, HasSubstr("UPPER_CASE"));
    }
  }
  EXPECT_TRUE(found_nam_003) << "Should detect NAM_003 for parameter naming";
}

}  // namespace
}  // namespace tools
}  // namespace verilog

