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

#include "verible/verilog/tools/veripg/rule-config.h"

#include "gtest/gtest.h"

namespace verilog {
namespace tools {
namespace {

// Test: Default configuration
TEST(RuleConfigTest, DefaultConfiguration) {
  ValidatorConfig config;
  config.SetDefaults();
  
  // All rules should be enabled by default
  EXPECT_TRUE(config.IsRuleEnabled(RuleId::kCDC_001));
  EXPECT_TRUE(config.IsRuleEnabled(RuleId::kCLK_001));
  EXPECT_TRUE(config.IsRuleEnabled(RuleId::kNAM_001));
  
  // Default severity should be Warning
  EXPECT_EQ(config.GetRuleSeverity(RuleId::kCDC_001), Severity::kWarning);
}

// Test: Enable/disable rules
TEST(RuleConfigTest, EnableDisableRules) {
  ValidatorConfig config;
  config.SetDefaults();
  
  // Disable specific rule
  config.SetRuleEnabled(RuleId::kCDC_001, false);
  EXPECT_FALSE(config.IsRuleEnabled(RuleId::kCDC_001));
  EXPECT_TRUE(config.IsRuleEnabled(RuleId::kCLK_001));  // Others still enabled
  
  // Re-enable
  config.SetRuleEnabled(RuleId::kCDC_001, true);
  EXPECT_TRUE(config.IsRuleEnabled(RuleId::kCDC_001));
}

// Test: Set severity
TEST(RuleConfigTest, SetSeverity) {
  ValidatorConfig config;
  config.SetDefaults();
  
  // Change severity to Error
  config.SetRuleSeverity(RuleId::kCDC_001, Severity::kError);
  EXPECT_EQ(config.GetRuleSeverity(RuleId::kCDC_001), Severity::kError);
  
  // Other rules unchanged
  EXPECT_EQ(config.GetRuleSeverity(RuleId::kCLK_001), Severity::kWarning);
}

// Test: File exclusions
TEST(RuleConfigTest, FileExclusions) {
  ValidatorConfig config;
  config.SetDefaults();
  
  // Add file exclusion
  config.AddFileExclusion(RuleId::kCDC_001, "*_tb.sv");
  
  // Check exclusion matching
  EXPECT_TRUE(config.ShouldExclude(RuleId::kCDC_001, "test_tb.sv", ""));
  EXPECT_FALSE(config.ShouldExclude(RuleId::kCDC_001, "test.sv", ""));
  EXPECT_FALSE(config.ShouldExclude(RuleId::kCLK_001, "test_tb.sv", ""));  // Different rule
}

// Test: Module exclusions
TEST(RuleConfigTest, ModuleExclusions) {
  ValidatorConfig config;
  config.SetDefaults();
  
  // Add module exclusion
  config.AddModuleExclusion(RuleId::kNAM_001, "legacy_*");
  
  // Check exclusion matching
  EXPECT_TRUE(config.ShouldExclude(RuleId::kNAM_001, "", "legacy_module"));
  EXPECT_FALSE(config.ShouldExclude(RuleId::kNAM_001, "", "new_module"));
}

// Test: Rule parameters
TEST(RuleConfigTest, RuleParameters) {
  ValidatorConfig config;
  config.SetDefaults();
  
  // Set parameter
  config.SetRuleParameter(RuleId::kSTR_002, "max_statements", "100");
  
  // Get parameter
  const auto& rule_config = config.GetRuleConfig(RuleId::kSTR_002);
  auto it = rule_config.parameters.find("max_statements");
  ASSERT_NE(it, rule_config.parameters.end());
  EXPECT_EQ(it->second, "100");
}

}  // namespace
}  // namespace tools
}  // namespace verilog
