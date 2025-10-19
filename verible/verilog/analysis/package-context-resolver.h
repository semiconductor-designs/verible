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

// PackageContextResolver parses SystemVerilog package files and extracts
// their context (macros, types) for use when parsing test files.
//
// Feature 3 (v5.4.0): Package Context Mode

#ifndef VERIBLE_VERILOG_ANALYSIS_PACKAGE_CONTEXT_RESOLVER_H_
#define VERIBLE_VERILOG_ANALYSIS_PACKAGE_CONTEXT_RESOLVER_H_

#include <memory>
#include <string>
#include <string_view>
#include <vector>

#include "absl/status/statusor.h"
#include "verible/verilog/analysis/include-file-resolver.h"
#include "verible/verilog/analysis/package-context.h"

namespace verilog {

// Parses package files and extracts their context
class PackageContextResolver {
 public:
  // Constructor accepts include resolver for resolving includes within packages
  explicit PackageContextResolver(IncludeFileResolver* include_resolver, 
                                  bool enable_includes = true)
      : include_resolver_(include_resolver), enable_includes_(enable_includes) {}

  // Parse a single package file and extract its context
  //
  // Args:
  //   package_file: Path to package file (e.g., "dv_base_test_pkg.sv")
  //
  // Returns:
  //   PackageContext with macros, types, and imports
  //   Error if file not found or parsing fails
  absl::StatusOr<PackageContext> ParsePackage(std::string_view package_file);

  // Parse multiple packages and combine their contexts
  //
  // Args:
  //   package_files: List of package files to process
  //
  // Returns:
  //   CombinedPackageContext with all macros and types
  //   Error if any file fails to parse
  //
  // Note: Packages are processed in order. Later packages can override
  //       macros from earlier packages.
  absl::StatusOr<CombinedPackageContext> ParsePackages(
      const std::vector<std::string>& package_files);

  // Auto-detect package file based on test file path
  //
  // Heuristics:
  //   - test_pkg/my_test.sv → test_pkg/test_pkg.sv
  //   - dv/tests/my_test.sv → dv/tests/tests_pkg.sv
  //   - dir/file.sv → dir/dir_pkg.sv
  //
  // Args:
  //   test_file: Path to test file
  //
  // Returns:
  //   Path to detected package file
  //   Error if no package file found
  absl::StatusOr<std::string> AutoDetectPackageFile(
      std::string_view test_file);

 private:
  IncludeFileResolver* include_resolver_;  // Not owned
  bool enable_includes_;  // Whether to process include directives in packages

  // Extract macro definitions from parsed package
  // Uses include_resolver_ to process `include directives
  absl::Status ExtractMacros(const class VerilogAnalyzer& analyzer,
                             PackageContext* context);

  // Extract type definitions (class, typedef, enum names)
  // Walks the syntax tree to find type declarations
  absl::Status ExtractTypes(const class VerilogAnalyzer& analyzer,
                           PackageContext* context);

  // Extract import statements
  // Tracks package dependencies for future enhancement
  absl::Status ExtractImports(const class VerilogAnalyzer& analyzer,
                             PackageContext* context);

  // Extract package name from "package name;" declaration
  absl::StatusOr<std::string> ExtractPackageName(
      const class VerilogAnalyzer& analyzer);
};

}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_PACKAGE_CONTEXT_RESOLVER_H_

