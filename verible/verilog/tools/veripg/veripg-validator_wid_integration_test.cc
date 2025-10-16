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

class VeriPGValidatorWIDIntegrationTest : public ::testing::Test {
 protected:
  // Note: type_checker is created per-test with the actual symbol_table
};

// Test WID_001: Signal width mismatch in assignment
TEST_F(VeriPGValidatorWIDIntegrationTest, DetectSignalWidthMismatch) {
  const std::string test_file = 
      "verible/verilog/tools/veripg/testdata/wid_signal_width_mismatch.sv";
  
  VerilogProject project(".", {});
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
  
  auto status = validator.CheckWidthViolations(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  bool found_wid_001 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kWID_001) {
      found_wid_001 = true;
      EXPECT_EQ(v.severity, Severity::kWarning);
      EXPECT_THAT(v.message, HasSubstr("width"));
    }
  }
  EXPECT_TRUE(found_wid_001) << "Should detect WID_001 for width mismatch";
}

// Test WID_002: Implicit width conversion (lossy)
TEST_F(VeriPGValidatorWIDIntegrationTest, DetectImplicitConversion) {
  const std::string test_file = 
      "verible/verilog/tools/veripg/testdata/wid_implicit_conversion.sv";
  
  VerilogProject project(".", {});
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
  
  auto status = validator.CheckWidthViolations(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  bool found_wid_002 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kWID_002) {
      found_wid_002 = true;
      EXPECT_EQ(v.severity, Severity::kWarning);
      EXPECT_THAT(v.message, HasSubstr("implicit"));
    }
  }
  EXPECT_TRUE(found_wid_002) << "Should detect WID_002 for implicit conversion";
}

// Test WID_003: Concatenation width mismatch
TEST_F(VeriPGValidatorWIDIntegrationTest, DetectConcatenationMismatch) {
  const std::string test_file = 
      "verible/verilog/tools/veripg/testdata/wid_concatenation_mismatch.sv";
  
  VerilogProject project(".", {});
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
  
  auto status = validator.CheckWidthViolations(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  bool found_wid_003 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kWID_003) {
      found_wid_003 = true;
      EXPECT_EQ(v.severity, Severity::kWarning);
      EXPECT_THAT(v.message, HasSubstr("concatenation"));
    }
  }
  EXPECT_TRUE(found_wid_003) << "Should detect WID_003 for concatenation mismatch";
}

// Test WID_004: Parameter width inconsistent with usage
TEST_F(VeriPGValidatorWIDIntegrationTest, DetectParameterWidthInconsistency) {
  const std::string test_file = 
      "verible/verilog/tools/veripg/testdata/wid_parameter_width.sv";
  
  VerilogProject project(".", {});
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
  
  auto status = validator.CheckWidthViolations(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  bool found_wid_004 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kWID_004) {
      found_wid_004 = true;
      EXPECT_EQ(v.severity, Severity::kWarning);
      EXPECT_THAT(v.message, HasSubstr("parameter"));
    }
  }
  EXPECT_TRUE(found_wid_004) << "Should detect WID_004 for parameter width inconsistency";
}

// Test WID_005: Port width mismatch in instantiation
TEST_F(VeriPGValidatorWIDIntegrationTest, DetectPortWidthMismatch) {
  const std::string test_file = 
      "verible/verilog/tools/veripg/testdata/wid_port_instantiation.sv";
  
  VerilogProject project(".", {});
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
  
  auto status = validator.CheckWidthViolations(symbol_table, violations, &project);
  ASSERT_TRUE(status.ok()) << status.message();
  
  bool found_wid_005 = false;
  for (const auto& v : violations) {
    if (v.rule == RuleId::kWID_005) {
      found_wid_005 = true;
      EXPECT_EQ(v.severity, Severity::kWarning);
      EXPECT_THAT(v.message, HasSubstr("port"));
    }
  }
  EXPECT_TRUE(found_wid_005) << "Should detect WID_005 for port width mismatch";
}

}  // namespace
}  // namespace tools
}  // namespace verilog
