// Copyright 2017-2020 The Verible Authors.
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

// MacroErrorSuggestions provides helpful error messages for undefined macros.
// It detects common macro patterns (UVM, OpenTitan) and suggests solutions.

#ifndef VERIBLE_VERILOG_PREPROCESSOR_MACRO_ERROR_SUGGESTIONS_H_
#define VERIBLE_VERILOG_PREPROCESSOR_MACRO_ERROR_SUGGESTIONS_H_

#include <string>
#include <string_view>
#include <vector>

namespace verilog {

// Returns enhanced error message with suggestions for undefined macro
std::string GetMacroErrorWithSuggestions(
    std::string_view macro_name,
    std::string_view current_file,
    const std::vector<std::string>& include_paths);

// Checks if macro is a known UVM macro
bool IsKnownUVMMacro(std::string_view macro_name);

// Checks if macro is a known OpenTitan macro
bool IsKnownOpenTitanMacro(std::string_view macro_name);

// Suggests package file based on current file path
std::string SuggestPackageFile(std::string_view current_file);

}  // namespace verilog

#endif  // VERIBLE_VERILOG_PREPROCESSOR_MACRO_ERROR_SUGGESTIONS_H_

