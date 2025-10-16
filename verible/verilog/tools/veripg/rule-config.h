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

#ifndef VERIBLE_VERILOG_TOOLS_VERIPG_RULE_CONFIG_H_
#define VERIBLE_VERILOG_TOOLS_VERIPG_RULE_CONFIG_H_

#include <string>
#include <vector>
#include <map>

#include "absl/status/statusor.h"
#include "verible/verilog/tools/veripg/veripg-validator.h"

namespace verilog {
namespace tools {

// Configuration for a single validation rule
struct RuleConfig {
  RuleId rule_id;
  bool enabled = true;
  Severity severity = Severity::kError;
  std::vector<std::string> exceptions;  // File patterns to exclude
  std::map<std::string, std::string> parameters;  // Rule-specific parameters
};

// Complete validator configuration
class ValidatorConfig {
 public:
  ValidatorConfig() = default;
  
  // Load configuration from YAML file
  static absl::StatusOr<ValidatorConfig> LoadFromYAML(
      const std::string& yaml_path);
  
  // Load configuration from JSON file
  static absl::StatusOr<ValidatorConfig> LoadFromJSON(
      const std::string& json_path);
  
  // Get configuration for a specific rule
  const RuleConfig* GetRuleConfig(RuleId rule_id) const;
  
  // Check if a rule is enabled
  bool IsRuleEnabled(RuleId rule_id) const;
  
  // Get severity for a rule (returns configured severity or default)
  Severity GetRuleSeverity(RuleId rule_id) const;
  
  // Check if a file matches any exception pattern for a rule
  bool IsFileExcepted(RuleId rule_id, const std::string& file_path) const;
  
  // Add or update rule configuration
  void SetRuleConfig(const RuleConfig& config);
  
  // Get all rule configurations
  const std::map<RuleId, RuleConfig>& GetAllRuleConfigs() const {
    return rule_configs_;
  }

 private:
  std::map<RuleId, RuleConfig> rule_configs_;
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_VERIPG_RULE_CONFIG_H_

