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
  kSafe,      // Always safe to apply automatically
  kUnsafe     // Requires human review before applying
};

// A single code fix with metadata
struct AutoFix {
  RuleId rule;
  FixSafety safety;
  std::string description;
  std::string old_code;  // Code to be replaced
  std::string new_code;  // Replacement code
  int line_start;
  int line_end;
};

// Auto-fix engine for generating code fixes
class AutoFixEngine {
 public:
  AutoFixEngine() = default;
  
  // Generate fix for a violation
  AutoFix GenerateFixForViolation(const Violation& violation) const;
  
  // Apply fixes to source code
  absl::Status ApplyFixes(const std::string& source_code,
                          const std::vector<AutoFix>& fixes,
                          std::string& fixed_code) const;
  
  // Rule-specific fix generators
  AutoFix GenerateFixCDC_001(const Violation& v) const;
  AutoFix GenerateFixCLK_001(const Violation& v) const;
  AutoFix GenerateFixRST_001(const Violation& v) const;
  AutoFix GenerateFixNAM_001(const Violation& v) const;
  AutoFix GenerateFixWID_001(const Violation& v) const;
  AutoFix GenerateFixSTR_005(const Violation& v) const;
  AutoFix GenerateFixSTR_006(const Violation& v) const;
  
 private:
  // Helper to detect fix safety level
  FixSafety DetectFixSafety(RuleId rule) const;
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_VERIPG_AUTO_FIX_ENGINE_H_
