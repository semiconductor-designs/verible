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

#include "verible/verilog/tools/veripg/auto-fix-engine.h"

#include "absl/strings/str_cat.h"
#include "absl/strings/str_replace.h"

namespace verilog {
namespace tools {

// Generate fix for a violation
AutoFix AutoFixEngine::GenerateFixForViolation(const Violation& violation) const {
  switch (violation.rule) {
    case RuleId::kCDC_001:
      return GenerateFixCDC_001(violation);
    case RuleId::kCLK_001:
      return GenerateFixCLK_001(violation);
    case RuleId::kRST_001:
      return GenerateFixRST_001(violation);
    case RuleId::kNAM_001:
      return GenerateFixNAM_001(violation);
    case RuleId::kWID_001:
      return GenerateFixWID_001(violation);
    case RuleId::kSTR_005:
      return GenerateFixSTR_005(violation);
    case RuleId::kSTR_006:
      return GenerateFixSTR_006(violation);
    default:
      // No auto-fix available for this rule
      AutoFix fix;
      fix.rule = violation.rule;
      fix.safety = FixSafety::kUnsafe;
      fix.description = "No automatic fix available";
      fix.old_code = "";
      fix.new_code = "";
      fix.line_start = 0;
      fix.line_end = 0;
      return fix;
  }
}

// Apply fixes to source code
absl::Status AutoFixEngine::ApplyFixes(const std::string& source_code,
                                       const std::vector<AutoFix>& fixes,
                                       std::string& fixed_code) const {
  // Simplified framework implementation
  // Full implementation would handle line-based replacements
  
  fixed_code = source_code;
  
  for (const auto& fix : fixes) {
    if (fix.safety == FixSafety::kSafe && !fix.old_code.empty()) {
      fixed_code = absl::StrReplaceAll(fixed_code, {{fix.old_code, fix.new_code}});
    }
  }
  
  return absl::OkStatus();
}

// CDC_001: Add synchronizer
AutoFix AutoFixEngine::GenerateFixCDC_001(const Violation& v) const {
  AutoFix fix;
  fix.rule = RuleId::kCDC_001;
  fix.safety = FixSafety::kUnsafe;  // Requires design review
  fix.description = "Add 2-stage synchronizer for CDC signal";
  fix.old_code = "";  // Would need CST to extract
  fix.new_code = absl::StrCat(
      "logic ", v.signal_name, "_sync1, ", v.signal_name, "_sync2;\n",
      "always_ff @(posedge dest_clk) begin\n",
      "  ", v.signal_name, "_sync1 <= ", v.signal_name, ";\n",
      "  ", v.signal_name, "_sync2 <= ", v.signal_name, "_sync1;\n",
      "end"
  );
  fix.line_start = 0;
  fix.line_end = 0;
  return fix;
}

// CLK_001: Add missing clock
AutoFix AutoFixEngine::GenerateFixCLK_001(const Violation& v) const {
  AutoFix fix;
  fix.rule = RuleId::kCLK_001;
  fix.safety = FixSafety::kSafe;
  fix.description = "Add clock signal to sensitivity list";
  fix.old_code = "always_ff begin";
  fix.new_code = "always_ff @(posedge clk) begin";
  fix.line_start = 0;
  fix.line_end = 0;
  return fix;
}

// RST_001: Add missing reset
AutoFix AutoFixEngine::GenerateFixRST_001(const Violation& v) const {
  AutoFix fix;
  fix.rule = RuleId::kRST_001;
  fix.safety = FixSafety::kUnsafe;  // Requires design review for reset behavior
  fix.description = "Add reset to sensitivity list";
  fix.old_code = "always_ff @(posedge clk)";
  fix.new_code = "always_ff @(posedge clk or negedge rst_n)";
  fix.line_start = 0;
  fix.line_end = 0;
  return fix;
}

// NAM_001: Convert to snake_case
AutoFix AutoFixEngine::GenerateFixNAM_001(const Violation& v) const {
  AutoFix fix;
  fix.rule = RuleId::kNAM_001;
  fix.safety = FixSafety::kSafe;  // Naming changes are generally safe
  fix.description = "Convert module name to snake_case";
  
  // Convert signal_name from PascalCase to snake_case
  std::string snake_case;
  for (size_t i = 0; i < v.signal_name.length(); ++i) {
    char c = v.signal_name[i];
    if (i > 0 && std::isupper(c)) {
      snake_case += '_';
    }
    snake_case += std::tolower(c);
  }
  
  fix.old_code = absl::StrCat("module ", v.signal_name);
  fix.new_code = absl::StrCat("module ", snake_case);
  fix.line_start = 0;
  fix.line_end = 0;
  return fix;
}

// WID_001: Add explicit width cast
AutoFix AutoFixEngine::GenerateFixWID_001(const Violation& v) const {
  AutoFix fix;
  fix.rule = RuleId::kWID_001;
  fix.safety = FixSafety::kUnsafe;  // Width changes can alter behavior
  fix.description = "Add explicit width cast";
  fix.old_code = "";  // Would need CST context
  fix.new_code = "";  // Would generate cast based on widths
  fix.line_start = 0;
  fix.line_end = 0;
  return fix;
}

// STR_005: Reorder ports
AutoFix AutoFixEngine::GenerateFixSTR_005(const Violation& v) const {
  AutoFix fix;
  fix.rule = RuleId::kSTR_005;
  fix.safety = FixSafety::kSafe;
  fix.description = "Reorder ports to: clk, rst, inputs, outputs";
  fix.old_code = "";  // Would need full port list
  fix.new_code = "";  // Would generate reordered ports
  fix.line_start = 0;
  fix.line_end = 0;
  return fix;
}

// STR_006: Convert to named ports
AutoFix AutoFixEngine::GenerateFixSTR_006(const Violation& v) const {
  AutoFix fix;
  fix.rule = RuleId::kSTR_006;
  fix.safety = FixSafety::kSafe;
  fix.description = "Convert positional ports to named ports";
  fix.old_code = "";  // Would need instantiation context
  fix.new_code = "";  // Would generate named port connections
  fix.line_start = 0;
  fix.line_end = 0;
  return fix;
}

// Helper to detect fix safety level
FixSafety AutoFixEngine::DetectFixSafety(RuleId rule) const {
  switch (rule) {
    case RuleId::kCLK_001:
    case RuleId::kNAM_001:
    case RuleId::kNAM_002:
    case RuleId::kNAM_003:
    case RuleId::kSTR_005:
    case RuleId::kSTR_006:
      return FixSafety::kSafe;
    
    default:
      return FixSafety::kUnsafe;
  }
}

}  // namespace tools
}  // namespace verilog
