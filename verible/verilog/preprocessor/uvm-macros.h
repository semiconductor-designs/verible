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

// UVM Macro Registry
// Provides built-in definitions for common UVM macros to enable parsing
// of UVM testbenches without requiring external UVM library files.
//
// This is Phase 2.1 of the UVM Enhancement project.
// See: UVM_PHASE2_GRAMMAR_ANALYSIS.md

#ifndef VERIBLE_VERILOG_PREPROCESSOR_UVM_MACROS_H_
#define VERIBLE_VERILOG_PREPROCESSOR_UVM_MACROS_H_

#include <map>
#include <string_view>
#include <vector>

#include "verible/common/text/macro-definition.h"

namespace verilog {
namespace preprocessor {

// Returns a map of UVM macro names to their definitions.
// This registry contains common UVM macros that need special handling
// during preprocessing.
const std::map<std::string_view, verible::MacroDefinition>& GetUvmMacroRegistry();

// Returns a list of UVM macro names that are known to be complex
// and might require special parsing or expansion logic.
const std::vector<std::string_view>& GetComplexUvmMacroNames();

}  // namespace preprocessor
}  // namespace verilog

#endif  // VERIBLE_VERILOG_PREPROCESSOR_UVM_MACROS_H_

