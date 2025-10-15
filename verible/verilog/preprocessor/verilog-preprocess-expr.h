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

// SV-2023 Enhanced Preprocessor Expression Evaluator
// Supports logical operators in `ifdef conditions: &&, ||, !, ->, <->

#ifndef VERIBLE_VERILOG_PREPROCESSOR_VERILOG_PREPROCESS_EXPR_H_
#define VERIBLE_VERILOG_PREPROCESSOR_VERILOG_PREPROCESS_EXPR_H_

#include <map>
#include <string>
#include <string_view>
#include "absl/status/statusor.h"

namespace verilog {

// Evaluates a preprocessor conditional expression with SV-2023 logical operators
// expr: The expression string (e.g., "A && B", "!C", "A -> B")
// defined_macros: Map of macro names to their defined state
// Returns: true if condition is met, false otherwise, or error status
absl::StatusOr<bool> EvaluatePreprocessorExpression(
    std::string_view expr,
    const std::map<std::string_view, bool>& defined_macros);

}  // namespace verilog

#endif  // VERIBLE_VERILOG_PREPROCESSOR_VERILOG_PREPROCESS_EXPR_H_

