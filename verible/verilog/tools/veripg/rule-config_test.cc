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

#include "verible/verilog/tools/veripg/rule-config.h"

#include "gtest/gtest.h"

namespace verilog {
namespace tools {
namespace {

// Test 1: ValidatorConfig construction
TEST(RuleConfigTest, DefaultConstruction) {
  ValidatorConfig config;
  EXPECT_TRUE(config.GetAllRuleConfigs().empty());
}

// Test 2: Set and get rule config
TEST(RuleConfigTest, SetAndGetRuleConfig) {
  ValidatorConfig config;
  
  RuleConfig rule;
  rule.rule_id = RuleId::kCDC_001;
  rule.enabled = true;
  rule.severity = Severity::kError;
  
  config.SetRuleConfig(rule);
  
  const RuleConfig* retrieved = config.GetRuleConfig(RuleId::kCDC_001);
  ASSERT_NE(retrieved, nullptr);
  EXPECT_EQ(retrieved->rule_id, RuleId::kCDC_001);
  EXPECT_TRUE(retrieved->enabled);
  EXPECT_EQ(retrieved->severity, Severity::kError);
}

// Test 3: IsRuleEnabled - enabled rule
TEST(RuleConfigTest, IsRuleEnabled_Enabled) {
  ValidatorConfig config;
  
  RuleConfig rule;
  rule.rule_id = RuleId::kNAM_001;
  rule.enabled = true;
  
  config.SetRuleConfig(rule);
  EXPECT_TRUE(config.IsRuleEnabled(RuleId::kNAM_001));
}

// Test 4: IsRuleEnabled - disabled rule
TEST(RuleConfigTest, IsRuleEnabled_Disabled) {
  ValidatorConfig config;
  
  RuleConfig rule;
  rule.rule_id = RuleId::kNAM_001;
  rule.enabled = false;
  
  config.SetRuleConfig(rule);
  EXPECT_FALSE(config.IsRuleEnabled(RuleId::kNAM_001));
}

// Test 5: IsRuleEnabled - default (no config)
TEST(RuleConfigTest, IsRuleEnabled_Default) {
  ValidatorConfig config;
  // No config set, should default to enabled
  EXPECT_TRUE(config.IsRuleEnabled(RuleId::kCDC_001));
}

// Test 6: GetRuleSeverity - configured
TEST(RuleConfigTest, GetRuleSeverity_Configured) {
  ValidatorConfig config;
  
  RuleConfig rule;
  rule.rule_id = RuleId::kWID_001;
  rule.severity = Severity::kWarning;
  
  config.SetRuleConfig(rule);
  EXPECT_EQ(config.GetRuleSeverity(RuleId::kWID_001), Severity::kWarning);
}

// Test 7: GetRuleSeverity - default
TEST(RuleConfigTest, GetRuleSeverity_Default) {
  ValidatorConfig config;
  // No config, should default to Error
  EXPECT_EQ(config.GetRuleSeverity(RuleId::kCDC_001), Severity::kError);
}

// Test 8: IsFileExcepted - no exceptions
TEST(RuleConfigTest, IsFileExcepted_NoExceptions) {
  ValidatorConfig config;
  
  RuleConfig rule;
  rule.rule_id = RuleId::kSTR_001;
  
  config.SetRuleConfig(rule);
  EXPECT_FALSE(config.IsFileExcepted(RuleId::kSTR_001, "test.sv"));
}

// Test 9: IsFileExcepted - with exception match
TEST(RuleConfigTest, IsFileExcepted_Match) {
  ValidatorConfig config;
  
  RuleConfig rule;
  rule.rule_id = RuleId::kSTR_001;
  rule.exceptions = {"_tb.sv", "testbench/"};
  
  config.SetRuleConfig(rule);
  EXPECT_TRUE(config.IsFileExcepted(RuleId::kSTR_001, "uart_tx_tb.sv"));
  EXPECT_TRUE(config.IsFileExcepted(RuleId::kSTR_001, "testbench/top_tb.sv"));
  EXPECT_FALSE(config.IsFileExcepted(RuleId::kSTR_001, "uart_tx.sv"));
}

// Test 10: Multiple rules configuration
TEST(RuleConfigTest, MultipleRules) {
  ValidatorConfig config;
  
  RuleConfig cdc_rule;
  cdc_rule.rule_id = RuleId::kCDC_001;
  cdc_rule.enabled = true;
  
  RuleConfig nam_rule;
  nam_rule.rule_id = RuleId::kNAM_001;
  nam_rule.enabled = false;
  
  config.SetRuleConfig(cdc_rule);
  config.SetRuleConfig(nam_rule);
  
  EXPECT_EQ(config.GetAllRuleConfigs().size(), 2);
  EXPECT_TRUE(config.IsRuleEnabled(RuleId::kCDC_001));
  EXPECT_FALSE(config.IsRuleEnabled(RuleId::kNAM_001));
}

// Test 11: LoadFromYAML framework
TEST(RuleConfigTest, LoadFromYAML_Framework) {
  auto result = ValidatorConfig::LoadFromYAML("test.yaml");
  EXPECT_TRUE(result.ok());
}

// Test 12: LoadFromJSON framework
TEST(RuleConfigTest, LoadFromJSON_Framework) {
  auto result = ValidatorConfig::LoadFromJSON("test.json");
  EXPECT_TRUE(result.ok());
}

}  // namespace
}  // namespace tools
}  // namespace verilog

