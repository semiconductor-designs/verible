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

#ifndef VERIBLE_VERILOG_TOOLS_VERIPG_OUTPUT_FORMATTER_H_
#define VERIBLE_VERILOG_TOOLS_VERIPG_OUTPUT_FORMATTER_H_

#include <string>
#include <vector>

#include "verible/verilog/tools/veripg/veripg-validator.h"

namespace verilog {
namespace tools {

// Output format types
enum class OutputFormat {
  kText,    // Human-readable text format
  kJSON,    // Machine-readable JSON format
  kSARIF    // SARIF 2.1.0 format for CI/CD integration
};

// Output formatter for validation results
class OutputFormatter {
 public:
  explicit OutputFormatter(OutputFormat format) : format_(format) {}
  
  // Format violations as text (default, human-readable)
  std::string FormatAsText(const std::vector<Violation>& violations) const;
  
  // Format violations as JSON (machine-readable)
  std::string FormatAsJSON(const std::vector<Violation>& violations) const;
  
  // Format violations as SARIF 2.1.0 (CI/CD integration)
  std::string FormatAsSARIF(const std::vector<Violation>& violations,
                            const std::string& tool_version = "5.0.0") const;
  
  // Format violations using the configured format
  std::string Format(const std::vector<Violation>& violations) const;
  
  // Get summary statistics
  struct Statistics {
    int total_violations = 0;
    int errors = 0;
    int warnings = 0;
    int info = 0;
  };
  
  Statistics GetStatistics(const std::vector<Violation>& violations) const;

 private:
  OutputFormat format_;
  
  // Helper functions for JSON formatting
  std::string EscapeJSON(const std::string& str) const;
  std::string SeverityToString(Severity severity) const;
  std::string RuleIdToString(RuleId rule_id) const;
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_VERIPG_OUTPUT_FORMATTER_H_

