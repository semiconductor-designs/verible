// Copyright 2025 The Verible Authors.
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

#include "gtest/gtest.h"

namespace verilog {
namespace tools {
namespace {

// Test 1: FormatAsText - no violations
TEST(OutputFormatterTest, FormatAsText_NoViolations) {
  OutputFormatter formatter(OutputFormat::kText);
  std::vector<Violation> violations;
  
  std::string output = formatter.FormatAsText(violations);
  
  EXPECT_NE(output.find("No violations"), std::string::npos);
}

// Test 2: FormatAsText - single violation
TEST(OutputFormatterTest, FormatAsText_SingleViolation) {
  OutputFormatter formatter(OutputFormat::kText);
  
  Violation v;
  v.rule = RuleId::kCDC_001;
  v.severity = Severity::kError;
  v.message = "CDC without synchronizer";
  v.source_location = "test.sv:10:5";
  v.signal_name = "data_signal";
  
  std::vector<Violation> violations = {v};
  std::string output = formatter.FormatAsText(violations);
  
  EXPECT_NE(output.find("ERROR"), std::string::npos);
  EXPECT_NE(output.find("CDC_001"), std::string::npos);
  EXPECT_NE(output.find("test.sv:10:5"), std::string::npos);
}

// Test 3: FormatAsJSON - empty violations
TEST(OutputFormatterTest, FormatAsJSON_Empty) {
  OutputFormatter formatter(OutputFormat::kJSON);
  std::vector<Violation> violations;
  
  std::string output = formatter.FormatAsJSON(violations);
  
  EXPECT_NE(output.find("\"total\": 0"), std::string::npos);
  EXPECT_NE(output.find("\"violations\": ["), std::string::npos);
}

// Test 4: FormatAsJSON - single violation
TEST(OutputFormatterTest, FormatAsJSON_SingleViolation) {
  OutputFormatter formatter(OutputFormat::kJSON);
  
  Violation v;
  v.rule = RuleId::kNAM_001;
  v.severity = Severity::kWarning;
  v.message = "Module name should be lowercase";
  v.source_location = "test.sv:5:1";
  
  std::vector<Violation> violations = {v};
  std::string output = formatter.FormatAsJSON(violations);
  
  EXPECT_NE(output.find("\"rule\": \"NAM_001\""), std::string::npos);
  EXPECT_NE(output.find("\"severity\": \"warning\""), std::string::npos);
}

// Test 5: FormatAsSARIF - basic structure
TEST(OutputFormatterTest, FormatAsSARIF_Structure) {
  OutputFormatter formatter(OutputFormat::kSARIF);
  std::vector<Violation> violations;
  
  std::string output = formatter.FormatAsSARIF(violations, "5.0.0");
  
  EXPECT_NE(output.find("\"version\": \"2.1.0\""), std::string::npos);
  EXPECT_NE(output.find("\"name\": \"VeriPG Validator\""), std::string::npos);
  EXPECT_NE(output.find("\"version\": \"5.0.0\""), std::string::npos);
}

// Test 6: FormatAsSARIF - single violation
TEST(OutputFormatterTest, FormatAsSARIF_SingleViolation) {
  OutputFormatter formatter(OutputFormat::kSARIF);
  
  Violation v;
  v.rule = RuleId::kWID_001;
  v.severity = Severity::kError;
  v.message = "Width mismatch";
  v.source_location = "test.sv:15:3";
  
  std::vector<Violation> violations = {v};
  std::string output = formatter.FormatAsSARIF(violations);
  
  EXPECT_NE(output.find("\"ruleId\": \"WID_001\""), std::string::npos);
  EXPECT_NE(output.find("\"level\": \"error\""), std::string::npos);
}

// Test 7: Format - uses configured format (Text)
TEST(OutputFormatterTest, Format_Text) {
  OutputFormatter formatter(OutputFormat::kText);
  std::vector<Violation> violations;
  
  std::string output = formatter.Format(violations);
  
  EXPECT_NE(output.find("VeriPG Validation Report"), std::string::npos);
}

// Test 8: Format - uses configured format (JSON)
TEST(OutputFormatterTest, Format_JSON) {
  OutputFormatter formatter(OutputFormat::kJSON);
  std::vector<Violation> violations;
  
  std::string output = formatter.Format(violations);
  
  EXPECT_NE(output.find("\"summary\""), std::string::npos);
}

// Test 9: Format - uses configured format (SARIF)
TEST(OutputFormatterTest, Format_SARIF) {
  OutputFormatter formatter(OutputFormat::kSARIF);
  std::vector<Violation> violations;
  
  std::string output = formatter.Format(violations);
  
  EXPECT_NE(output.find("\"runs\""), std::string::npos);
}

// Test 10: GetStatistics - empty
TEST(OutputFormatterTest, GetStatistics_Empty) {
  OutputFormatter formatter(OutputFormat::kText);
  std::vector<Violation> violations;
  
  auto stats = formatter.GetStatistics(violations);
  
  EXPECT_EQ(stats.total_violations, 0);
  EXPECT_EQ(stats.errors, 0);
  EXPECT_EQ(stats.warnings, 0);
  EXPECT_EQ(stats.info, 0);
}

// Test 11: GetStatistics - mixed severities
TEST(OutputFormatterTest, GetStatistics_Mixed) {
  OutputFormatter formatter(OutputFormat::kText);
  
  std::vector<Violation> violations;
  Violation v1;
  v1.severity = Severity::kError;
  violations.push_back(v1);
  
  Violation v2;
  v2.severity = Severity::kWarning;
  violations.push_back(v2);
  
  Violation v3;
  v3.severity = Severity::kInfo;
  violations.push_back(v3);
  
  auto stats = formatter.GetStatistics(violations);
  
  EXPECT_EQ(stats.total_violations, 3);
  EXPECT_EQ(stats.errors, 1);
  EXPECT_EQ(stats.warnings, 1);
  EXPECT_EQ(stats.info, 1);
}

// Test 12: All 3 output formats work
TEST(OutputFormatterTest, AllFormatsWork) {
  Violation v;
  v.rule = RuleId::kSTR_005;
  v.severity = Severity::kWarning;
  v.message = "Port ordering";
  std::vector<Violation> violations = {v};
  
  OutputFormatter text_formatter(OutputFormat::kText);
  OutputFormatter json_formatter(OutputFormat::kJSON);
  OutputFormatter sarif_formatter(OutputFormat::kSARIF);
  
  std::string text_output = text_formatter.Format(violations);
  std::string json_output = json_formatter.Format(violations);
  std::string sarif_output = sarif_formatter.Format(violations);
  
  EXPECT_FALSE(text_output.empty());
  EXPECT_FALSE(json_output.empty());
  EXPECT_FALSE(sarif_output.empty());
  
  // Each format should be unique
  EXPECT_NE(text_output, json_output);
  EXPECT_NE(json_output, sarif_output);
  EXPECT_NE(text_output, sarif_output);
}

// Test 13: JSON escaping works
TEST(OutputFormatterTest, JSONEscaping) {
  OutputFormatter formatter(OutputFormat::kJSON);
  
  Violation v;
  v.rule = RuleId::kNAM_001;
  v.severity = Severity::kError;
  v.message = "Test \"quotes\" and \\backslash\\ and \nnewline";
  
  std::vector<Violation> violations = {v};
  std::string output = formatter.FormatAsJSON(violations);
  
  EXPECT_NE(output.find("\\\""), std::string::npos);  // Escaped quote
  EXPECT_NE(output.find("\\\\"), std::string::npos);  // Escaped backslash
  EXPECT_NE(output.find("\\n"), std::string::npos);   // Escaped newline
}

// Test 14: SARIF severity mapping
TEST(OutputFormatterTest, SARIFSeverityMapping) {
  OutputFormatter formatter(OutputFormat::kSARIF);
  
  std::vector<Violation> violations;
  
  Violation v1;
  v1.rule = RuleId::kCDC_001;
  v1.severity = Severity::kError;
  v1.message = "Error test";
  violations.push_back(v1);
  
  Violation v2;
  v2.rule = RuleId::kNAM_001;
  v2.severity = Severity::kWarning;
  v2.message = "Warning test";
  violations.push_back(v2);
  
  Violation v3;
  v3.rule = RuleId::kSTR_004;
  v3.severity = Severity::kInfo;
  v3.message = "Info test";
  violations.push_back(v3);
  
  std::string output = formatter.FormatAsSARIF(violations);
  
  EXPECT_NE(output.find("\"level\": \"error\""), std::string::npos);
  EXPECT_NE(output.find("\"level\": \"warning\""), std::string::npos);
  EXPECT_NE(output.find("\"level\": \"note\""), std::string::npos);
}

// Test 15: Fix suggestions in SARIF
TEST(OutputFormatterTest, SARIFFixSuggestions) {
  OutputFormatter formatter(OutputFormat::kSARIF);
  
  Violation v;
  v.rule = RuleId::kNAM_001;
  v.severity = Severity::kWarning;
  v.message = "Module name incorrect";
  v.fix_suggestion = "Rename to lowercase_with_underscores";
  
  std::vector<Violation> violations = {v};
  std::string output = formatter.FormatAsSARIF(violations);
  
  EXPECT_NE(output.find("\"fixes\""), std::string::npos);
  EXPECT_NE(output.find("lowercase_with_underscores"), std::string::npos);
}

// Test 16: Multiple violations in all formats
TEST(OutputFormatterTest, MultipleViolationsAllFormats) {
  std::vector<Violation> violations;
  
  for (int i = 0; i < 5; ++i) {
    Violation v;
    v.rule = RuleId::kCDC_001;
    v.severity = (i % 2 == 0) ? Severity::kError : Severity::kWarning;
    v.message = "Test violation";
    violations.push_back(v);
  }
  
  OutputFormatter text_formatter(OutputFormat::kText);
  OutputFormatter json_formatter(OutputFormat::kJSON);
  OutputFormatter sarif_formatter(OutputFormat::kSARIF);
  
  std::string text = text_formatter.Format(violations);
  std::string json = json_formatter.Format(violations);
  std::string sarif = sarif_formatter.Format(violations);
  
  // All should contain 5 violations
  auto text_stats = text_formatter.GetStatistics(violations);
  EXPECT_EQ(text_stats.total_violations, 5);
}

}  // namespace
}  // namespace tools
}  // namespace verilog

