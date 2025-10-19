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

// PackageContext represents the context from a SystemVerilog package file
// for parsing other files in that package context.
//
// Feature 3 (v5.4.0): Package Context Mode
//
// OpenTitan UVM testbench files are designed for package-based compilation.
// This allows parsing test files with the macro and type context from their
// package file, eliminating the need for explicit includes.
//
// Example:
//   // dv_base_test_pkg.sv
//   package dv_base_test_pkg;
//     `include "uvm_macros.svh"
//     `define CUSTOM_MACRO 42
//     class dv_base_test extends uvm_test;
//       // ...
//     endclass
//   endpackage
//
//   // my_test.sv (parsed with package context)
//   class my_custom_test extends dv_base_test;
//     int value = `CUSTOM_MACRO;  // Works with package context!
//   endclass

#ifndef VERIBLE_VERILOG_ANALYSIS_PACKAGE_CONTEXT_H_
#define VERIBLE_VERILOG_ANALYSIS_PACKAGE_CONTEXT_H_

#include <map>
#include <memory>
#include <string>
#include <string_view>
#include <vector>

#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/preprocessor/verilog-preprocess.h"

namespace verilog {

// Context extracted from a single SystemVerilog package file
struct PackageContext {
  // Name of the package (extracted from "package name;")
  std::string package_name;

  // Macro definitions from the package (including from `include directives)
  // NOTE: These MacroDefinitions contain string_views pointing to memory
  // owned by the analyzer below. Do not use these after analyzer is destroyed!
  VerilogPreprocessData::MacroDefinitionRegistry macro_definitions;

  // Type definitions (class names, typedefs, enums)
  // For v5.4.0: Just track names for validation
  // For v5.5.0: Full type information for symbol table seeding
  std::vector<std::string> type_names;

  // Import statements (for future dependency tracking)
  std::vector<std::string> imports;

  // Source file path
  std::string source_file;

  // Analyzer must be kept alive because macro_definitions contain string_views
  // pointing to memory owned by the analyzer
  std::unique_ptr<VerilogAnalyzer> analyzer;
};

// Combined context from multiple packages
struct CombinedPackageContext {
  // All packages in order of processing
  std::vector<PackageContext> packages;

  // Flattened view of all macros (for easy lookup)
  VerilogPreprocessData::MacroDefinitionRegistry all_macros;

  // Flattened view of all type names (for validation)
  std::vector<std::string> all_types;

  // Returns true if any packages have been loaded
  bool HasContext() const { return !packages.empty(); }

  // Returns the number of macros available
  size_t MacroCount() const { return all_macros.size(); }

  // Returns the number of type names available
  size_t TypeCount() const { return all_types.size(); }
};

}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_PACKAGE_CONTEXT_H_

