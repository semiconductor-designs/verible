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

#ifndef VERIBLE_VERILOG_TOOLS_REFACTOR_REFACTORING_ENGINE_H_
#define VERIBLE_VERILOG_TOOLS_REFACTOR_REFACTORING_ENGINE_H_

#include <string>

#include "absl/status/status.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-inference.h"

namespace verilog {
namespace tools {

// Selection in source code (for extract operations)
struct Selection {
  int start_line = 0;
  int start_column = 0;
  int end_line = 0;
  int end_column = 0;
};

// Location in source code
struct Location {
  std::string filename;
  int line = 0;
  int column = 0;
};

// RefactoringEngine provides advanced code transformations
class RefactoringEngine {
 public:
  // Construct with symbol table and type inference
  explicit RefactoringEngine(const verilog::SymbolTable* symbol_table,
                              const verilog::analysis::TypeInference* type_inference);

  // Extract selected code into new function
  absl::Status ExtractFunction(const Selection& selection,
                                const std::string& function_name);

  // Inline function at call site
  absl::Status InlineFunction(const Location& call_site);

  // Extract expression into variable
  absl::Status ExtractVariable(const Selection& selection,
                                const std::string& var_name);

  // Move declaration to optimal scope
  absl::Status MoveDeclaration(const Location& decl_location);

 private:
  const verilog::SymbolTable* symbol_table_;
  const verilog::analysis::TypeInference* type_inference_;
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_REFACTOR_REFACTORING_ENGINE_H_

