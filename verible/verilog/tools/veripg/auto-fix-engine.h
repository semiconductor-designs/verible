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

#ifndef VERIBLE_VERILOG_TOOLS_VERIPG_AUTO_FIX_ENGINE_H_
#define VERIBLE_VERILOG_TOOLS_VERIPG_AUTO_FIX_ENGINE_H_

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "verible/verilog/tools/veripg/veripg-validator.h"

namespace verilog {
namespace tools {

// Classification of fix safety
enum class FixSafety {
  kSafe,    // Can be applied automatically (e.g., add whitespace, rename)
  kUnsafe   // Requires manual review (e.g., logic changes, signal routing)
};

// Single fix suggestion
struct FixSuggestion {
  RuleId rule_id;
  FixSafety safety;
  std::string description;
  std::string code_snippet;  // Suggested replacement code
  int line_number = 0;
  int column_number = 0;
};

// Auto-fix engine for VeriPG validation violations
class AutoFixEngine {
 public:
  AutoFixEngine() = default;
  
  // Generate fix suggestion for a violation
  FixSuggestion GenerateFix(const Violation& violation);
  
  // Generate fixes for all violations
  std::vector<FixSuggestion> GenerateFixes(
      const std::vector<Violation>& violations);
  
  // Apply safe fixes automatically (returns number of fixes applied)
  absl::Status ApplySafeFixes(
      const std::string& file_path,
      const std::vector<FixSuggestion>& fixes,
      int* fixes_applied);
  
  // Individual fix generators (10+ as specified in plan)
  
  // CDC/Clock/Reset fixes
  std::string GenerateFixCDC_001(const Violation& v);  // Add synchronizer
  std::string GenerateFixCLK_001(const Violation& v);  // Add clock signal
  std::string GenerateFixRST_001(const Violation& v);  // Add reset logic
  
  // Naming fixes
  std::string GenerateFixNAM_001(const Violation& v);  // Module naming
  std::string GenerateFixNAM_003(const Violation& v);  // Parameter naming
  std::string GenerateFixNAM_004(const Violation& v);  // Clock naming
  std::string GenerateFixNAM_005(const Violation& v);  // Reset naming
  
  // Width fixes
  std::string GenerateFixWID_001(const Violation& v);  // Width cast
  
  // Structure fixes
  std::string GenerateFixSTR_005(const Violation& v);  // Port ordering
  std::string GenerateFixSTR_006(const Violation& v);  // Named ports
  std::string GenerateFixSTR_007(const Violation& v);  // Generate labels
  std::string GenerateFixSTR_008(const Violation& v);  // Default clause
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_VERIPG_AUTO_FIX_ENGINE_H_

