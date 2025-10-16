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

#include <algorithm>
#include <fstream>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"

namespace verilog {
namespace tools {

// Load configuration from YAML file
absl::StatusOr<ValidatorConfig> ValidatorConfig::LoadFromYAML(
    const std::string& yaml_path) {
  // Simplified framework implementation
  // Full implementation would use yaml-cpp or similar library
  
  ValidatorConfig config;
  config.SetDefaults();
  
  // Framework: Return default config
  // TODO: Parse YAML file and populate rule_configs_
  
  return config;
}

// Load configuration from JSON file
absl::StatusOr<ValidatorConfig> ValidatorConfig::LoadFromJSON(
    const std::string& json_path) {
  // Simplified framework implementation
  // Full implementation would use JSON parser
  
  ValidatorConfig config;
  config.SetDefaults();
  
  // Framework: Return default config
  // TODO: Parse JSON file and populate rule_configs_
  
  return config;
}

// Get configuration for specific rule
const RuleConfig& ValidatorConfig::GetRuleConfig(RuleId rule_id) const {
  auto it = rule_configs_.find(rule_id);
  if (it != rule_configs_.end()) {
    return it->second;
  }
  return default_config_;
}

// Check if rule is enabled
bool ValidatorConfig::IsRuleEnabled(RuleId rule_id) const {
  return GetRuleConfig(rule_id).enabled;
}

// Get severity for rule
Severity ValidatorConfig::GetRuleSeverity(RuleId rule_id) const {
  return GetRuleConfig(rule_id).severity;
}

// Check if file/module should be excluded for this rule
bool ValidatorConfig::ShouldExclude(RuleId rule_id,
                                    const std::string& file_path,
                                    const std::string& module_name) const {
  const auto& config = GetRuleConfig(rule_id);
  
  // Check file exclusions
  for (const auto& pattern : config.exclude_files) {
    if (MatchesPattern(file_path, pattern)) {
      return true;
    }
  }
  
  // Check module exclusions
  for (const auto& pattern : config.exclude_modules) {
    if (MatchesPattern(module_name, pattern)) {
      return true;
    }
  }
  
  return false;
}

// Set default configuration
void ValidatorConfig::SetDefaults() {
  // All rules enabled with Warning severity by default
  default_config_.enabled = true;
  default_config_.severity = Severity::kWarning;
}

// Enable/disable specific rule
void ValidatorConfig::SetRuleEnabled(RuleId rule_id, bool enabled) {
  rule_configs_[rule_id].enabled = enabled;
}

// Set severity for specific rule
void ValidatorConfig::SetRuleSeverity(RuleId rule_id, Severity severity) {
  rule_configs_[rule_id].severity = severity;
}

// Add file exclusion pattern for rule
void ValidatorConfig::AddFileExclusion(RuleId rule_id, 
                                       const std::string& pattern) {
  rule_configs_[rule_id].exclude_files.push_back(pattern);
}

// Add module exclusion pattern for rule
void ValidatorConfig::AddModuleExclusion(RuleId rule_id,
                                         const std::string& pattern) {
  rule_configs_[rule_id].exclude_modules.push_back(pattern);
}

// Set parameter for rule
void ValidatorConfig::SetRuleParameter(RuleId rule_id,
                                       const std::string& param_name,
                                       const std::string& param_value) {
  rule_configs_[rule_id].parameters[param_name] = param_value;
}

// Helper to match glob patterns
bool ValidatorConfig::MatchesPattern(const std::string& text,
                                     const std::string& pattern) const {
  // Simplified pattern matching (supports * wildcard)
  // Full implementation would use fnmatch or similar
  
  if (pattern == "*") return true;
  
  // Check for trailing wildcard: "test_*"
  if (pattern.back() == '*') {
    std::string prefix = pattern.substr(0, pattern.size() - 1);
    return absl::StartsWith(text, prefix);
  }
  
  // Check for leading wildcard: "*_tb"
  if (pattern.front() == '*') {
    std::string suffix = pattern.substr(1);
    return absl::EndsWith(text, suffix);
  }
  
  // Exact match
  return text == pattern;
}

}  // namespace tools
}  // namespace verilog
