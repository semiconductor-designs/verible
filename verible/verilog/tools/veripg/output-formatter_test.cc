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

#include "verible/verilog/tools/veripg/output-formatter.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace verilog {
namespace tools {
namespace {

// Test: Format empty violations as text
TEST(OutputFormatterTest, FormatEmptyAsText) {
  OutputFormatter formatter(OutputFormat::kText);
  std::vector<Violation> violations;
  
  std::string output = formatter.FormatAsText(violations);
  
  EXPECT_THAT(output, testing::HasSubstr("No violations found"));
}

// Test: Format single violation as text
TEST(OutputFormatterTest, FormatSingleViolationAsText) {
  OutputFormatter formatter(OutputFormat::kText);
  
  Violation v;
  v.rule = RuleId::kCDC_001;
  v.severity = Severity::kError;
  v.message = "CDC without synchronizer";
  v.signal_name = "async_signal";
  v.source_location = "test.sv:10:5";
  
  std::vector<Violation> violations = {v};
  std::string output = formatter.FormatAsText(violations);
  
  EXPECT_THAT(output, testing::HasSubstr("CDC_001"));
  EXPECT_THAT(output, testing::HasSubstr("CDC without synchronizer"));
  EXPECT_THAT(output, testing::HasSubstr("async_signal"));
  EXPECT_THAT(output, testing::HasSubstr("test.sv:10:5"));
}

// Test: Format as JSON
TEST(OutputFormatterTest, FormatAsJSON) {
  OutputFormatter formatter(OutputFormat::kJSON);
  
  Violation v;
  v.rule = RuleId::kCLK_001;
  v.severity = Severity::kWarning;
  v.message = "Missing clock signal";
  v.signal_name = "data_reg";
  v.source_location = "test.sv:20:10";
  
  std::vector<Violation> violations = {v};
  std::string output = formatter.FormatAsJSON(violations);
  
  EXPECT_THAT(output, testing::HasSubstr("\"rule\":"));
  EXPECT_THAT(output, testing::HasSubstr("\"severity\":"));
  EXPECT_THAT(output, testing::HasSubstr("\"message\":"));
  EXPECT_THAT(output, testing::HasSubstr("Missing clock signal"));
}

// Test: Format as SARIF
TEST(OutputFormatterTest, FormatAsSARIF) {
  OutputFormatter formatter(OutputFormat::kSARIF);
  
  Violation v;
  v.rule = RuleId::kRST_001;
  v.severity = Severity::kError;
  v.message = "Missing reset signal";
  v.signal_name = "state_reg";
  v.source_location = "test.sv:30:15";
  
  std::vector<Violation> violations = {v};
  std::string output = formatter.FormatAsSARIF(violations);
  
  EXPECT_THAT(output, testing::HasSubstr("\"$schema\":"));
  EXPECT_THAT(output, testing::HasSubstr("\"version\":"));
  EXPECT_THAT(output, testing::HasSubstr("\"results\":"));
  EXPECT_THAT(output, testing::HasSubstr("Missing reset signal"));
}

// Test: Format with configured format
TEST(OutputFormatterTest, FormatWithConfiguredFormat) {
  Violation v;
  v.rule = RuleId::kNAM_001;
  v.severity = Severity::kWarning;
  v.message = "Module naming violation";
  
  std::vector<Violation> violations = {v};
  
  // Text format
  OutputFormatter text_formatter(OutputFormat::kText);
  std::string text_output = text_formatter.Format(violations);
  EXPECT_THAT(text_output, testing::HasSubstr("Module naming violation"));
  
  // JSON format
  OutputFormatter json_formatter(OutputFormat::kJSON);
  std::string json_output = json_formatter.Format(violations);
  EXPECT_THAT(json_output, testing::HasSubstr("\"message\":"));
  
  // SARIF format
  OutputFormatter sarif_formatter(OutputFormat::kSARIF);
  std::string sarif_output = sarif_formatter.Format(violations);
  EXPECT_THAT(sarif_output, testing::HasSubstr("\"$schema\":"));
}

// Test: Get statistics
TEST(OutputFormatterTest, GetStatistics) {
  OutputFormatter formatter(OutputFormat::kText);
  
  std::vector<Violation> violations;
  
  Violation v1;
  v1.severity = Severity::kError;
  violations.push_back(v1);
  
  Violation v2;
  v2.severity = Severity::kWarning;
  violations.push_back(v2);
  
  Violation v3;
  v3.severity = Severity::kWarning;
  violations.push_back(v3);
  
  Violation v4;
  v4.severity = Severity::kInfo;
  violations.push_back(v4);
  
  auto stats = formatter.GetStatistics(violations);
  
  EXPECT_EQ(stats.total_violations, 4);
  EXPECT_EQ(stats.errors, 1);
  EXPECT_EQ(stats.warnings, 2);
  EXPECT_EQ(stats.info, 1);
}

// Test: Empty violations statistics
TEST(OutputFormatterTest, EmptyStatistics) {
  OutputFormatter formatter(OutputFormat::kText);
  std::vector<Violation> violations;
  
  auto stats = formatter.GetStatistics(violations);
  
  EXPECT_EQ(stats.total_violations, 0);
  EXPECT_EQ(stats.errors, 0);
  EXPECT_EQ(stats.warnings, 0);
  EXPECT_EQ(stats.info, 0);
}

}  // namespace
}  // namespace tools
}  // namespace verilog
