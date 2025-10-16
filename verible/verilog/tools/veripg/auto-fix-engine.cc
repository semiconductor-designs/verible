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

#include "verible/verilog/tools/veripg/auto-fix-engine.h"

#include <fstream>
#include <cctype>

#include "absl/strings/str_cat.h"

namespace verilog {
namespace tools {

FixSuggestion AutoFixEngine::GenerateFix(const Violation& violation) {
  FixSuggestion fix;
  fix.rule_id = violation.rule;
  
  // Route to appropriate fix generator based on rule ID
  switch (violation.rule) {
    case RuleId::kCDC_001:
      fix.code_snippet = GenerateFixCDC_001(violation);
      fix.safety = FixSafety::kUnsafe;  // Requires logic changes
      break;
    case RuleId::kCLK_001:
      fix.code_snippet = GenerateFixCLK_001(violation);
      fix.safety = FixSafety::kUnsafe;  // Requires sensitivity list change
      break;
    case RuleId::kRST_001:
      fix.code_snippet = GenerateFixRST_001(violation);
      fix.safety = FixSafety::kUnsafe;  // Requires logic changes
      break;
    case RuleId::kNAM_001:
      fix.code_snippet = GenerateFixNAM_001(violation);
      fix.safety = FixSafety::kSafe;  // Pure renaming
      break;
    case RuleId::kNAM_003:
      fix.code_snippet = GenerateFixNAM_003(violation);
      fix.safety = FixSafety::kSafe;  // Pure renaming
      break;
    case RuleId::kNAM_004:
      fix.code_snippet = GenerateFixNAM_004(violation);
      fix.safety = FixSafety::kSafe;  // Pure renaming
      break;
    case RuleId::kNAM_005:
      fix.code_snippet = GenerateFixNAM_005(violation);
      fix.safety = FixSafety::kSafe;  // Pure renaming
      break;
    case RuleId::kWID_001:
      fix.code_snippet = GenerateFixWID_001(violation);
      fix.safety = FixSafety::kUnsafe;  // Type changes
      break;
    case RuleId::kSTR_005:
      fix.code_snippet = GenerateFixSTR_005(violation);
      fix.safety = FixSafety::kUnsafe;  // Port order changes
      break;
    case RuleId::kSTR_006:
      fix.code_snippet = GenerateFixSTR_006(violation);
      fix.safety = FixSafety::kSafe;  // Equivalent transformation
      break;
    case RuleId::kSTR_007:
      fix.code_snippet = GenerateFixSTR_007(violation);
      fix.safety = FixSafety::kSafe;  // Add label only
      break;
    case RuleId::kSTR_008:
      fix.code_snippet = GenerateFixSTR_008(violation);
      fix.safety = FixSafety::kUnsafe;  // Logic changes
      break;
    default:
      fix.code_snippet = "// No auto-fix available for this rule";
      fix.safety = FixSafety::kUnsafe;
      break;
  }
  
  fix.description = violation.message;
  return fix;
}

std::vector<FixSuggestion> AutoFixEngine::GenerateFixes(
    const std::vector<Violation>& violations) {
  std::vector<FixSuggestion> fixes;
  for (const auto& violation : violations) {
    fixes.push_back(GenerateFix(violation));
  }
  return fixes;
}

absl::Status AutoFixEngine::ApplySafeFixes(
    const std::string& file_path,
    const std::vector<FixSuggestion>& fixes,
    int* fixes_applied) {
  // Apply safe fixes automatically
  //
  // Implementation strategy:
  // 1. Read file content
  // 2. Filter for safe fixes only
  // 3. Apply fixes in reverse line order (to preserve line numbers)
  // 4. Write back to file (with backup)
  //
  // For framework purposes, return success
  
  *fixes_applied = 0;
  
  // TODO: Implement actual file modification
  // Would integrate with SymbolRenamer for naming fixes
  
  return absl::OkStatus();
}

// ========================================
// Individual Fix Generators
// ========================================

std::string AutoFixEngine::GenerateFixCDC_001(const Violation& v) {
  return absl::StrCat(
      "  // Add 2-stage synchronizer for: ", v.signal_name, "\n",
      "  logic ", v.signal_name, "_sync1, ", v.signal_name, "_sync2;\n",
      "  always_ff @(posedge dest_clk) begin\n",
      "    ", v.signal_name, "_sync1 <= ", v.signal_name, ";\n",
      "    ", v.signal_name, "_sync2 <= ", v.signal_name, "_sync1;\n",
      "  end\n"
  );
}

std::string AutoFixEngine::GenerateFixCLK_001(const Violation& v) {
  return absl::StrCat(
      "  always_ff @(posedge clk) begin  // Added missing clock\n",
      "    // ... sequential logic\n",
      "  end\n"
  );
}

std::string AutoFixEngine::GenerateFixRST_001(const Violation& v) {
  return absl::StrCat(
      "  always_ff @(posedge clk or negedge rst_n) begin\n",
      "    if (!rst_n) begin  // Added missing reset\n",
      "      // Reset logic\n",
      "    end else begin\n",
      "      // Normal operation\n",
      "    end\n",
      "  end\n"
  );
}

std::string AutoFixEngine::GenerateFixNAM_001(const Violation& v) {
  // Convert module name to lowercase_with_underscores
  std::string fixed_name;
  for (size_t i = 0; i < v.signal_name.size(); ++i) {
    char c = v.signal_name[i];
    if (std::isupper(c)) {
      if (i > 0 && (std::islower(v.signal_name[i-1]) || 
                    std::isdigit(v.signal_name[i-1]))) {
        fixed_name += '_';
      } else if (i > 0 && std::isupper(v.signal_name[i-1]) && 
                 i + 1 < v.signal_name.size() && 
                 std::islower(v.signal_name[i+1])) {
        fixed_name += '_';
      }
      fixed_name += std::tolower(c);
    } else {
      fixed_name += c;
    }
  }
  return absl::StrCat("module ", fixed_name, ";  // Renamed from ", v.signal_name);
}

std::string AutoFixEngine::GenerateFixNAM_003(const Violation& v) {
  // Convert parameter name to UPPERCASE
  std::string fixed_name;
  for (char c : v.signal_name) {
    fixed_name += std::toupper(c);
  }
  return absl::StrCat("parameter ", fixed_name, " = ...;  // Renamed from ", v.signal_name);
}

std::string AutoFixEngine::GenerateFixNAM_004(const Violation& v) {
  return absl::StrCat("clk_", v.signal_name, "  // Renamed to start with 'clk_'");
}

std::string AutoFixEngine::GenerateFixNAM_005(const Violation& v) {
  return absl::StrCat("rst_", v.signal_name, "  // Renamed to start with 'rst_'");
}

std::string AutoFixEngine::GenerateFixWID_001(const Violation& v) {
  return absl::StrCat(
      "  ", v.signal_name, " = N'(expression);  // Added explicit width cast"
  );
}

std::string AutoFixEngine::GenerateFixSTR_005(const Violation& v) {
  return "  // Reorder ports: clk, rst, inputs, outputs\n"
         "  module name(input clk, input rst_n, input data, output result);";
}

std::string AutoFixEngine::GenerateFixSTR_006(const Violation& v) {
  return absl::StrCat(
      "  module_name ", v.signal_name, "(\n",
      "    .port1(signal1),  // Convert to named ports\n",
      "    .port2(signal2)\n",
      "  );"
  );
}

std::string AutoFixEngine::GenerateFixSTR_007(const Violation& v) {
  return "  begin : gen_label  // Added missing generate label";
}

std::string AutoFixEngine::GenerateFixSTR_008(const Violation& v) {
  return "    default: // Added missing default clause";
}

}  // namespace tools
}  // namespace verilog

