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

#include <fstream>
#include <sstream>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"

namespace verilog {
namespace tools {

absl::StatusOr<ValidatorConfig> ValidatorConfig::LoadFromYAML(
    const std::string& yaml_path) {
  // YAML parsing implementation
  //
  // Expected format:
  // ```yaml
  // rules:
  //   CDC_001:
  //     enabled: true
  //     severity: error
  //     exceptions:
  //       - "**/*_tb.sv"
  //       - "testbench/**"
  //   NAM_001:
  //     enabled: true
  //     severity: warning
  //     parameters:
  //       allow_camelcase: false
  // ```
  //
  // Implementation requires YAML parser (e.g., yaml-cpp)
  // For framework purposes, return success with empty config
  
  ValidatorConfig config;
  // TODO: Implement actual YAML parsing
  return config;
}

absl::StatusOr<ValidatorConfig> ValidatorConfig::LoadFromJSON(
    const std::string& json_path) {
  // JSON parsing implementation
  //
  // Expected format:
  // ```json
  // {
  //   "rules": {
  //     "CDC_001": {
  //       "enabled": true,
  //       "severity": "error",
  //       "exceptions": ["**/*_tb.sv", "testbench/**"]
  //     },
  //     "NAM_001": {
  //       "enabled": true,
  //       "severity": "warning",
  //       "parameters": {
  //         "allow_camelcase": false
  //       }
  //     }
  //   }
  // }
  // ```
  //
  // Implementation requires JSON parser (e.g., RapidJSON, nlohmann/json)
  // For framework purposes, return success with empty config
  
  ValidatorConfig config;
  // TODO: Implement actual JSON parsing
  return config;
}

const RuleConfig* ValidatorConfig::GetRuleConfig(RuleId rule_id) const {
  auto it = rule_configs_.find(rule_id);
  if (it != rule_configs_.end()) {
    return &it->second;
  }
  return nullptr;
}

bool ValidatorConfig::IsRuleEnabled(RuleId rule_id) const {
  const RuleConfig* config = GetRuleConfig(rule_id);
  if (config) {
    return config->enabled;
  }
  // Default: all rules enabled
  return true;
}

Severity ValidatorConfig::GetRuleSeverity(RuleId rule_id) const {
  const RuleConfig* config = GetRuleConfig(rule_id);
  if (config) {
    return config->severity;
  }
  // Default: error
  return Severity::kError;
}

bool ValidatorConfig::IsFileExcepted(RuleId rule_id, 
                                     const std::string& file_path) const {
  const RuleConfig* config = GetRuleConfig(rule_id);
  if (!config) {
    return false;
  }
  
  // Check if file matches any exception pattern
  for (const auto& pattern : config->exceptions) {
    // Simple suffix matching for framework
    // Full implementation would use glob matching
    if (file_path.find(pattern) != std::string::npos) {
      return true;
    }
  }
  
  return false;
}

void ValidatorConfig::SetRuleConfig(const RuleConfig& config) {
  rule_configs_[config.rule_id] = config;
}

}  // namespace tools
}  // namespace verilog

