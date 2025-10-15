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

#ifndef VERIBLE_VERILOG_ANALYSIS_UNUSED_DETECTOR_H_
#define VERIBLE_VERILOG_ANALYSIS_UNUSED_DETECTOR_H_

#include <map>
#include <set>
#include <string>
#include <string_view>
#include <vector>

#include "verible/verilog/analysis/symbol-table.h"

namespace verilog {
namespace analysis {

// Represents an unused symbol detection result.
struct UnusedSymbol {
  std::string name;                    // Symbol name
  std::string file_path;               // File where declared
  int line_number = 0;                 // Line number of declaration
  std::string symbol_type;             // Type (variable, function, parameter, etc.)
  std::string scope;                   // Scope where declared (module, class, etc.)
  
  // Constructor
  UnusedSymbol(std::string_view name, std::string_view file_path,
               int line_number, std::string_view symbol_type,
               std::string_view scope)
      : name(name), file_path(file_path), line_number(line_number),
        symbol_type(symbol_type), scope(scope) {}
};

// UnusedDetector analyzes a symbol table to find symbols that are declared
// but never referenced.
//
// Usage:
//   UnusedDetector detector(symbol_table);
//   detector.Analyze();
//   const auto& unused = detector.GetUnusedSymbols();
//   for (const auto& symbol : unused) {
//     std::cout << "Unused: " << symbol.name << " at "
//               << symbol.file_path << ":" << symbol.line_number << "\n";
//   }
class UnusedDetector {
 public:
  // Constructor takes a symbol table to analyze.
  explicit UnusedDetector(const SymbolTable* symbol_table);

  // Analyzes the symbol table to find unused symbols.
  // This method traverses the entire symbol table, identifies all declared
  // symbols, and checks if they are referenced anywhere.
  void Analyze();

  // Returns the list of unused symbols found by Analyze().
  const std::vector<UnusedSymbol>& GetUnusedSymbols() const {
    return unused_symbols_;
  }

  // Returns the count of unused symbols.
  size_t GetUnusedCount() const { return unused_symbols_.size(); }

  // Clears the analysis results.
  void Clear() { unused_symbols_.clear(); }

  // Configuration options for unused detection.
  struct Options {
    // If true, ignore parameters (they might be required by interface).
    bool ignore_parameters = false;
    
    // If true, ignore private members (prefixed with _).
    bool ignore_private = false;
    
    // If true, ignore symbols in testbenches.
    bool ignore_testbenches = false;
    
    // Minimum reference count to consider a symbol "used".
    // Default is 1 (any reference counts as used).
    int min_references = 1;
  };

  // Sets analysis options.
  void SetOptions(const Options& options) { options_ = options; }

  // Gets current options.
  const Options& GetOptions() const { return options_; }

 private:
  const SymbolTable* symbol_table_;
  std::vector<UnusedSymbol> unused_symbols_;
  Options options_;

  // Helper methods for analysis.
  void AnalyzeScope(const SymbolTableNode& scope);
  bool IsSymbolUsed(const SymbolTableNode& symbol) const;
  bool ShouldIgnoreSymbol(const SymbolInfo& info) const;
  std::string GetSymbolType(const SymbolInfo& info) const;
  std::string GetScopeName(const SymbolTableNode& scope) const;
};

}  // namespace analysis
}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_UNUSED_DETECTOR_H_

