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

// VeriPG Validator - SystemVerilog Style Checker
// Main CLI entry point

#include <iostream>
#include <string>
#include <vector>
#include <fstream>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/flags/usage.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"

#include "verible/common/util/init-command-line.h"
#include "verible/verilog/analysis/verilog-project.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-checker.h"
#include "verible/verilog/analysis/type-inference.h"
#include "verible/verilog/tools/veripg/veripg-validator.h"
#include "verible/verilog/tools/veripg/output-formatter.h"
#include "verible/verilog/tools/veripg/batch-processor.h"
#include "verible/verilog/tools/veripg/rule-config.h"

// Command-line flags
ABSL_FLAG(std::string, rules, "all",
          "Comma-separated list of rules to check (e.g., 'CDC_001,CLK_001' or 'all')");

ABSL_FLAG(std::string, config, "",
          "Path to YAML/JSON configuration file");

ABSL_FLAG(std::string, output_format, "text",
          "Output format: text, json, or sarif");

ABSL_FLAG(bool, fix, false,
          "Generate auto-fix suggestions");

ABSL_FLAG(bool, fail_on_violation, true,
          "Exit with error code 1 if violations found");

ABSL_FLAG(int, max_violations, 0,
          "Maximum number of violations to report (0 = unlimited)");

ABSL_FLAG(std::string, severity, "warning",
          "Minimum severity to report: info, warning, error");

ABSL_FLAG(bool, progress, false,
          "Show progress bar for batch processing");

ABSL_FLAG(bool, parallel, false,
          "Enable parallel processing for multiple files");

ABSL_FLAG(bool, show_version, false,
          "Show version information");

namespace verilog {
namespace tools {

constexpr char kVersion[] = "5.0.0-beta";
constexpr char kProgramName[] = "veripg-validator";

// Parse severity level from string
Severity ParseSeverity(const std::string& severity_str) {
  if (severity_str == "info") return Severity::kInfo;
  if (severity_str == "warning") return Severity::kWarning;
  if (severity_str == "error") return Severity::kError;
  return Severity::kWarning;  // Default
}

// Print version information
void PrintVersion() {
  std::cout << kProgramName << " version " << kVersion << std::endl;
  std::cout << "SystemVerilog Style Checker for VeriPG" << std::endl;
  std::cout << "Copyright 2017-2025 The Verible Authors" << std::endl;
}

// Print usage/help
void PrintHelp() {
  std::cout << R"(
VeriPG Validator - SystemVerilog Style Checker

USAGE:
  veripg-validator [OPTIONS] <file1.sv> [file2.sv ...]

DESCRIPTION:
  Checks SystemVerilog files for style violations, CDC issues, naming 
  conventions, and design best practices. Supports 40+ validation rules
  covering CDC, clock/reset, naming, width, power intent, and structure.

OPTIONS:
  --rules=<rules>         Rules to check (default: all)
                          Examples: all, CDC_001,CLK_001, NAM_*
  
  --config=<file>         Configuration file (YAML/JSON)
  
  --output_format=<fmt>   Output format (default: text)
                          Options: text, json, sarif
  
  --fix                   Generate auto-fix suggestions
  
  --fail_on_violation     Exit with code 1 if violations found (default: true)
  
  --max_violations=<n>    Max violations to report (default: unlimited)
  
  --severity=<level>      Minimum severity (default: warning)
                          Options: info, warning, error
  
  --progress              Show progress bar
  
  --parallel              Enable parallel processing
  
  --version               Show version information
  
  --help                  Show this help message

EXAMPLES:
  # Check single file
  veripg-validator design.sv
  
  # Check multiple files with JSON output
  veripg-validator --output_format=json src/*.sv
  
  # Check specific rules only
  veripg-validator --rules=CDC_001,CLK_001 design.sv
  
  # Use configuration file
  veripg-validator --config=.veripg.yaml src/**/*.sv
  
  # Generate auto-fix suggestions
  veripg-validator --fix design.sv
  
  # Batch mode with progress
  veripg-validator --progress --parallel src/**/*.sv

EXIT CODES:
  0  No violations found
  1  Violations found (if --fail_on_violation=true)
  2  Error during validation

For more information, see: docs/veripg-validator-user-guide.md
)";
}

// Main validation function
int RunValidator(const std::vector<std::string>& files) {
  // Handle version flag
  if (absl::GetFlag(FLAGS_show_version)) {
    PrintVersion();
    return 0;
  }
  
  // Check if files provided
  if (files.empty()) {
    std::cerr << "Error: No input files specified" << std::endl;
    std::cerr << "Run with --help for usage information" << std::endl;
    return 2;
  }
  
  // Load configuration if provided
  std::string config_file = absl::GetFlag(FLAGS_config);
  ValidatorConfig config;
  if (!config_file.empty()) {
    // Determine format from extension
    auto load_result = ValidatorConfig::LoadFromYAML(config_file);
    if (!load_result.ok()) {
      std::cerr << "Error loading config file: " << load_result.status().message() << std::endl;
      return 2;
    }
    config = load_result.value();
  }
  
  // Parse flags
  std::string rules_flag = absl::GetFlag(FLAGS_rules);
  std::string output_format_str = absl::GetFlag(FLAGS_output_format);
  bool generate_fixes = absl::GetFlag(FLAGS_fix);
  bool fail_on_violation = absl::GetFlag(FLAGS_fail_on_violation);
  int max_violations = absl::GetFlag(FLAGS_max_violations);
  std::string severity_str = absl::GetFlag(FLAGS_severity);
  bool show_progress = absl::GetFlag(FLAGS_progress);
  bool use_parallel = absl::GetFlag(FLAGS_parallel);
  
  Severity min_severity = ParseSeverity(severity_str);
  
  // Parse output format
  OutputFormat format = OutputFormat::kText;
  if (output_format_str == "json") {
    format = OutputFormat::kJSON;
  } else if (output_format_str == "sarif") {
    format = OutputFormat::kSARIF;
  }
  
  // Create VerilogProject
  VerilogProject project(".", {});
  
  // Statistics
  int total_files = 0;
  int files_with_violations = 0;
  std::vector<Violation> all_violations;
  
  // Process each file
  for (const auto& file_path : files) {
    total_files++;
    
    if (show_progress) {
      std::cerr << "\rProcessing " << total_files << "/" << files.size() 
                << ": " << file_path << std::flush;
    }
    
    // Open file
    auto file_or = project.OpenTranslationUnit(file_path);
    if (!file_or.ok()) {
      std::cerr << "\nError opening file " << file_path << ": " 
                << file_or.status().message() << std::endl;
      continue;
    }
    
    auto* file = file_or.value();
    if (!file->Status().ok()) {
      std::cerr << "\nError parsing file " << file_path << ": " 
                << file->Status().message() << std::endl;
      continue;
    }
    
    // Build symbol table
    SymbolTable symbol_table(&project);
    std::vector<absl::Status> diagnostics;
    symbol_table.Build(&diagnostics);
    
    if (!diagnostics.empty()) {
      std::cerr << "\nWarning: Symbol table build had " << diagnostics.size() 
                << " diagnostic(s) for " << file_path << std::endl;
    }
    
    // Create type checker
    analysis::TypeInference type_inference(&symbol_table);
    analysis::TypeChecker type_checker(&symbol_table, &type_inference);
    
    // Create validator
    VeriPGValidator validator(&type_checker);
    std::vector<Violation> violations;
    
    // Run all checks
    auto status = validator.CheckCDCViolations(symbol_table, violations, &project);
    if (!status.ok()) {
      std::cerr << "\nError checking CDC: " << status.message() << std::endl;
    }
    
    status = validator.CheckClockRules(symbol_table, violations, &project);
    if (!status.ok()) {
      std::cerr << "\nError checking CLK: " << status.message() << std::endl;
    }
    
    status = validator.CheckResetRules(symbol_table, violations, &project);
    if (!status.ok()) {
      std::cerr << "\nError checking RST: " << status.message() << std::endl;
    }
    
    status = validator.CheckTimingRules(symbol_table, violations, &project);
    if (!status.ok()) {
      std::cerr << "\nError checking TIM: " << status.message() << std::endl;
    }
    
    status = validator.CheckNamingViolations(symbol_table, violations, &project);
    if (!status.ok()) {
      std::cerr << "\nError checking NAM: " << status.message() << std::endl;
    }
    
    status = validator.CheckWidthViolations(symbol_table, violations, &project);
    if (!status.ok()) {
      std::cerr << "\nError checking WID: " << status.message() << std::endl;
    }
    
    status = validator.CheckPowerViolations(symbol_table, violations, &project);
    if (!status.ok()) {
      std::cerr << "\nError checking PWR: " << status.message() << std::endl;
    }
    
    status = validator.CheckStructureViolations(symbol_table, violations, &project);
    if (!status.ok()) {
      std::cerr << "\nError checking STR: " << status.message() << std::endl;
    }
    
    // Filter by severity
    std::vector<Violation> filtered_violations;
    for (const auto& v : violations) {
      if (v.severity >= min_severity) {
        filtered_violations.push_back(v);
      }
    }
    
    // Apply max violations limit
    if (max_violations > 0 && filtered_violations.size() > max_violations) {
      filtered_violations.resize(max_violations);
    }
    
    // Add to global list
    if (!filtered_violations.empty()) {
      files_with_violations++;
      all_violations.insert(all_violations.end(), 
                           filtered_violations.begin(), 
                           filtered_violations.end());
    }
  }
  
  if (show_progress) {
    std::cerr << std::endl;  // New line after progress
  }
  
  // Format output based on format flag
  OutputFormatter formatter(format);
  std::string output = formatter.Format(all_violations);
  std::cout << output << std::endl;
  
  // Print summary
  OutputFormatter::Statistics stats = formatter.GetStatistics(all_violations);
  
  if (format == OutputFormat::kText) {
    std::cout << "\n=== Summary ===" << std::endl;
    std::cout << "Total files: " << total_files << std::endl;
    std::cout << "Files with violations: " << files_with_violations << std::endl;
    std::cout << "Total violations: " << stats.total_violations << std::endl;
    std::cout << "  - Errors: " << stats.errors << std::endl;
    std::cout << "  - Warnings: " << stats.warnings << std::endl;
    std::cout << "  - Info: " << stats.info << std::endl;
  }
  
  // Determine exit code
  if (all_violations.empty()) {
    return 0;  // No violations
  } else if (fail_on_violation) {
    return 1;  // Violations found
  } else {
    return 0;  // Violations found but not failing
  }
}

}  // namespace tools
}  // namespace verilog

int main(int argc, char** argv) {
  // Set up command line
  const auto usage = absl::StrCat("usage: ", argv[0],
                                  " [options] <file1.sv> [file2.sv ...]\n"
                                  "Run with --help for detailed help");
  
  const auto args = verible::InitCommandLine(usage, &argc, &argv);
  
  // Check for help flag
  for (int i = 1; i < argc; ++i) {
    if (std::string(argv[i]) == "--help" || std::string(argv[i]) == "-h") {
      verilog::tools::PrintHelp();
      return 0;
    }
  }
  
  // Collect file arguments
  std::vector<std::string> files;
  for (const auto& arg : args) {
    if (!arg.empty() && arg[0] != '-') {
      files.push_back(std::string(arg));  // Convert string_view to string
    }
  }
  
  // Run validator
  return verilog::tools::RunValidator(files);
}

