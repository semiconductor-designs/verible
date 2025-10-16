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

#include <sstream>

#include "absl/strings/str_cat.h"

namespace verilog {
namespace tools {

std::string OutputFormatter::FormatAsText(
    const std::vector<Violation>& violations) const {
  std::ostringstream oss;
  
  auto stats = GetStatistics(violations);
  
  oss << "VeriPG Validation Report\n";
  oss << "========================\n\n";
  
  if (violations.empty()) {
    oss << "✅ No violations found!\n";
    return oss.str();
  }
  
  // Group by severity
  oss << "Summary:\n";
  oss << "  Errors:   " << stats.errors << "\n";
  oss << "  Warnings: " << stats.warnings << "\n";
  oss << "  Info:     " << stats.info << "\n";
  oss << "  Total:    " << stats.total_violations << "\n\n";
  
  oss << "Violations:\n";
  oss << "-----------\n\n";
  
  for (const auto& v : violations) {
    std::string severity_str;
    switch (v.severity) {
      case Severity::kError:   severity_str = "ERROR  "; break;
      case Severity::kWarning: severity_str = "WARNING"; break;
      case Severity::kInfo:    severity_str = "INFO   "; break;
    }
    
    oss << "[" << severity_str << "] " << RuleIdToString(v.rule) << "\n";
    oss << "  Location: " << v.source_location << "\n";
    oss << "  Message:  " << v.message << "\n";
    if (!v.signal_name.empty()) {
      oss << "  Signal:   " << v.signal_name << "\n";
    }
    if (!v.fix_suggestion.empty()) {
      oss << "  Fix:      " << v.fix_suggestion << "\n";
    }
    oss << "\n";
  }
  
  return oss.str();
}

std::string OutputFormatter::FormatAsJSON(
    const std::vector<Violation>& violations) const {
  std::ostringstream oss;
  
  auto stats = GetStatistics(violations);
  
  oss << "{\n";
  oss << "  \"summary\": {\n";
  oss << "    \"total\": " << stats.total_violations << ",\n";
  oss << "    \"errors\": " << stats.errors << ",\n";
  oss << "    \"warnings\": " << stats.warnings << ",\n";
  oss << "    \"info\": " << stats.info << "\n";
  oss << "  },\n";
  oss << "  \"violations\": [\n";
  
  for (size_t i = 0; i < violations.size(); ++i) {
    const auto& v = violations[i];
    
    oss << "    {\n";
    oss << "      \"rule\": \"" << RuleIdToString(v.rule) << "\",\n";
    oss << "      \"severity\": \"" << SeverityToString(v.severity) << "\",\n";
    oss << "      \"message\": \"" << EscapeJSON(v.message) << "\",\n";
    oss << "      \"location\": \"" << EscapeJSON(v.source_location) << "\"";
    
    if (!v.signal_name.empty()) {
      oss << ",\n      \"signal\": \"" << EscapeJSON(v.signal_name) << "\"";
    }
    if (!v.fix_suggestion.empty()) {
      oss << ",\n      \"fix\": \"" << EscapeJSON(v.fix_suggestion) << "\"";
    }
    
    oss << "\n    }";
    if (i < violations.size() - 1) {
      oss << ",";
    }
    oss << "\n";
  }
  
  oss << "  ]\n";
  oss << "}\n";
  
  return oss.str();
}

std::string OutputFormatter::FormatAsSARIF(
    const std::vector<Violation>& violations,
    const std::string& tool_version) const {
  // SARIF 2.1.0 format for CI/CD integration
  // https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html
  
  std::ostringstream oss;
  
  oss << "{\n";
  oss << "  \"version\": \"2.1.0\",\n";
  oss << "  \"$schema\": \"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\n";
  oss << "  \"runs\": [\n";
  oss << "    {\n";
  oss << "      \"tool\": {\n";
  oss << "        \"driver\": {\n";
  oss << "          \"name\": \"VeriPG Validator\",\n";
  oss << "          \"informationUri\": \"https://github.com/chipsalliance/verible\",\n";
  oss << "          \"version\": \"" << tool_version << "\"\n";
  oss << "        }\n";
  oss << "      },\n";
  oss << "      \"results\": [\n";
  
  for (size_t i = 0; i < violations.size(); ++i) {
    const auto& v = violations[i];
    
    std::string level;
    switch (v.severity) {
      case Severity::kError:   level = "error"; break;
      case Severity::kWarning: level = "warning"; break;
      case Severity::kInfo:    level = "note"; break;
    }
    
    oss << "        {\n";
    oss << "          \"ruleId\": \"" << RuleIdToString(v.rule) << "\",\n";
    oss << "          \"level\": \"" << level << "\",\n";
    oss << "          \"message\": {\n";
    oss << "            \"text\": \"" << EscapeJSON(v.message) << "\"\n";
    oss << "          },\n";
    oss << "          \"locations\": [\n";
    oss << "            {\n";
    oss << "              \"physicalLocation\": {\n";
    oss << "                \"artifactLocation\": {\n";
    oss << "                  \"uri\": \"" << EscapeJSON(v.source_location) << "\"\n";
    oss << "                }\n";
    oss << "              }\n";
    oss << "            }\n";
    oss << "          ]";
    
    if (!v.fix_suggestion.empty()) {
      oss << ",\n          \"fixes\": [\n";
      oss << "            {\n";
      oss << "              \"description\": {\n";
      oss << "                \"text\": \"" << EscapeJSON(v.fix_suggestion) << "\"\n";
      oss << "              }\n";
      oss << "            }\n";
      oss << "          ]";
    }
    
    oss << "\n        }";
    if (i < violations.size() - 1) {
      oss << ",";
    }
    oss << "\n";
  }
  
  oss << "      ]\n";
  oss << "    }\n";
  oss << "  ]\n";
  oss << "}\n";
  
  return oss.str();
}

std::string OutputFormatter::Format(
    const std::vector<Violation>& violations) const {
  switch (format_) {
    case OutputFormat::kText:
      return FormatAsText(violations);
    case OutputFormat::kJSON:
      return FormatAsJSON(violations);
    case OutputFormat::kSARIF:
      return FormatAsSARIF(violations);
    default:
      return FormatAsText(violations);
  }
}

OutputFormatter::Statistics OutputFormatter::GetStatistics(
    const std::vector<Violation>& violations) const {
  Statistics stats;
  stats.total_violations = violations.size();
  
  for (const auto& v : violations) {
    switch (v.severity) {
      case Severity::kError:
        stats.errors++;
        break;
      case Severity::kWarning:
        stats.warnings++;
        break;
      case Severity::kInfo:
        stats.info++;
        break;
    }
  }
  
  return stats;
}

std::string OutputFormatter::EscapeJSON(const std::string& str) const {
  std::string result;
  for (char c : str) {
    switch (c) {
      case '"':  result += "\\\""; break;
      case '\\': result += "\\\\"; break;
      case '\n': result += "\\n"; break;
      case '\r': result += "\\r"; break;
      case '\t': result += "\\t"; break;
      default:   result += c; break;
    }
  }
  return result;
}

std::string OutputFormatter::SeverityToString(Severity severity) const {
  switch (severity) {
    case Severity::kError:   return "error";
    case Severity::kWarning: return "warning";
    case Severity::kInfo:    return "info";
    default:                 return "unknown";
  }
}

std::string OutputFormatter::RuleIdToString(RuleId rule_id) const {
  // Map rule IDs to string representations
  switch (rule_id) {
    // CDC rules
    case RuleId::kCDC_001: return "CDC_001";
    case RuleId::kCDC_002: return "CDC_002";
    case RuleId::kCDC_003: return "CDC_003";
    case RuleId::kCDC_004: return "CDC_004";
    
    // Clock rules
    case RuleId::kCLK_001: return "CLK_001";
    case RuleId::kCLK_002: return "CLK_002";
    case RuleId::kCLK_003: return "CLK_003";
    case RuleId::kCLK_004: return "CLK_004";
    
    // Reset rules
    case RuleId::kRST_001: return "RST_001";
    case RuleId::kRST_002: return "RST_002";
    case RuleId::kRST_003: return "RST_003";
    case RuleId::kRST_004: return "RST_004";
    case RuleId::kRST_005: return "RST_005";
    
    // Timing rules
    case RuleId::kTIM_001: return "TIM_001";
    case RuleId::kTIM_002: return "TIM_002";
    
    // Naming rules
    case RuleId::kNAM_001: return "NAM_001";
    case RuleId::kNAM_002: return "NAM_002";
    case RuleId::kNAM_003: return "NAM_003";
    case RuleId::kNAM_004: return "NAM_004";
    case RuleId::kNAM_005: return "NAM_005";
    case RuleId::kNAM_006: return "NAM_006";
    case RuleId::kNAM_007: return "NAM_007";
    
    // Width rules
    case RuleId::kWID_001: return "WID_001";
    case RuleId::kWID_002: return "WID_002";
    case RuleId::kWID_003: return "WID_003";
    case RuleId::kWID_004: return "WID_004";
    case RuleId::kWID_005: return "WID_005";
    
    // Power rules
    case RuleId::kPWR_001: return "PWR_001";
    case RuleId::kPWR_002: return "PWR_002";
    case RuleId::kPWR_003: return "PWR_003";
    case RuleId::kPWR_004: return "PWR_004";
    case RuleId::kPWR_005: return "PWR_005";
    
    // Structure rules
    case RuleId::kSTR_001: return "STR_001";
    case RuleId::kSTR_002: return "STR_002";
    case RuleId::kSTR_003: return "STR_003";
    case RuleId::kSTR_004: return "STR_004";
    case RuleId::kSTR_005: return "STR_005";
    case RuleId::kSTR_006: return "STR_006";
    case RuleId::kSTR_007: return "STR_007";
    case RuleId::kSTR_008: return "STR_008";
    
    default: return "UNKNOWN";
  }
}

}  // namespace tools
}  // namespace verilog

