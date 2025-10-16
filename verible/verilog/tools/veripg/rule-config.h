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

#ifndef VERIBLE_VERILOG_TOOLS_VERIPG_RULE_CONFIG_H_
#define VERIBLE_VERILOG_TOOLS_VERIPG_RULE_CONFIG_H_

#include <map>
#include <set>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "verible/verilog/tools/veripg/veripg-validator.h"

namespace verilog {
namespace tools {

// Configuration for a single validation rule
struct RuleConfig {
  bool enabled = true;
  Severity severity = Severity::kWarning;
  
  // File/module exceptions (glob patterns)
  std::vector<std::string> exclude_files;
  std::vector<std::string> exclude_modules;
  
  // Rule-specific parameters
  std::map<std::string, std::string> parameters;
};

// Complete validator configuration
class ValidatorConfig {
 public:
  ValidatorConfig() = default;
  
  // Load configuration from YAML file
  static absl::StatusOr<ValidatorConfig> LoadFromYAML(const std::string& yaml_path);
  
  // Load configuration from JSON file
  static absl::StatusOr<ValidatorConfig> LoadFromJSON(const std::string& json_path);
  
  // Get configuration for specific rule
  const RuleConfig& GetRuleConfig(RuleId rule_id) const;
  
  // Check if rule is enabled
  bool IsRuleEnabled(RuleId rule_id) const;
  
  // Get severity for rule
  Severity GetRuleSeverity(RuleId rule_id) const;
  
  // Check if file/module should be excluded for this rule
  bool ShouldExclude(RuleId rule_id, 
                     const std::string& file_path,
                     const std::string& module_name) const;
  
  // Set default configuration (all rules enabled with default severity)
  void SetDefaults();
  
  // Enable/disable specific rule
  void SetRuleEnabled(RuleId rule_id, bool enabled);
  
  // Set severity for specific rule
  void SetRuleSeverity(RuleId rule_id, Severity severity);
  
  // Add file exclusion pattern for rule
  void AddFileExclusion(RuleId rule_id, const std::string& pattern);
  
  // Add module exclusion pattern for rule
  void AddModuleExclusion(RuleId rule_id, const std::string& pattern);
  
  // Set parameter for rule
  void SetRuleParameter(RuleId rule_id, 
                        const std::string& param_name,
                        const std::string& param_value);
  
 private:
  std::map<RuleId, RuleConfig> rule_configs_;
  
  // Default configuration for rules not explicitly configured
  RuleConfig default_config_;
  
  // Helper to match glob patterns
  bool MatchesPattern(const std::string& text, const std::string& pattern) const;
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_VERIPG_RULE_CONFIG_H_
