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

#include "verible/verilog/preprocessor/verilog-preprocess-expr.h"

#include <cctype>
#include <map>
#include <string>
#include <string_view>
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"

namespace verilog {
namespace {

// Simple preprocessor expression parser and evaluator
// Supports: identifiers, !, &&, ||, ->, <->, parentheses
class PreprocessorExpressionEvaluator {
 public:
  PreprocessorExpressionEvaluator(
      std::string_view expr,
      const std::map<std::string_view, bool>& defined_macros)
      : expr_(expr), pos_(0), defined_macros_(defined_macros) {}

  absl::StatusOr<bool> Evaluate() {
    auto result = ParseExpression();
    if (!result.ok()) return result.status();
    SkipWhitespace();
    if (pos_ < expr_.length()) {
      return absl::InvalidArgumentError(
          absl::StrCat("Unexpected characters after expression: ",
                      expr_.substr(pos_)));
    }
    return result.value();
  }

 private:
  void SkipWhitespace() {
    while (pos_ < expr_.length() && std::isspace(expr_[pos_])) {
      pos_++;
    }
  }

  // Parse equivalence (<->)
  absl::StatusOr<bool> ParseExpression() {
    auto left = ParseImplication();
    if (!left.ok()) return left.status();
    
    SkipWhitespace();
    if (pos_ + 2 < expr_.length() && expr_[pos_] == '<' &&
        expr_[pos_ + 1] == '-' && expr_[pos_ + 2] == '>') {
      pos_ += 3;
      auto right = ParseExpression();
      if (!right.ok()) return right.status();
      return *left == *right;  // Equivalence: A <-> B means A == B
    }
    return left;
  }

  // Parse implication (->)
  absl::StatusOr<bool> ParseImplication() {
    auto left = ParseOr();
    if (!left.ok()) return left.status();
    
    SkipWhitespace();
    if (pos_ + 1 < expr_.length() && expr_[pos_] == '-' &&
        expr_[pos_ + 1] == '>') {
      pos_ += 2;
      auto right = ParseImplication();
      if (!right.ok()) return right.status();
      return !*left || *right;  // Implication: A -> B means !A || B
    }
    return left;
  }

  // Parse logical OR (||)
  absl::StatusOr<bool> ParseOr() {
    auto left = ParseAnd();
    if (!left.ok()) return left.status();
    
    while (true) {
      SkipWhitespace();
      if (pos_ + 1 < expr_.length() && expr_[pos_] == '|' &&
          expr_[pos_ + 1] == '|') {
        pos_ += 2;
        auto right = ParseAnd();
        if (!right.ok()) return right.status();
        left = *left || *right;
      } else {
        break;
      }
    }
    return left;
  }

  // Parse logical AND (&&)
  absl::StatusOr<bool> ParseAnd() {
    auto left = ParseUnary();
    if (!left.ok()) return left.status();
    
    while (true) {
      SkipWhitespace();
      if (pos_ + 1 < expr_.length() && expr_[pos_] == '&' &&
          expr_[pos_ + 1] == '&') {
        pos_ += 2;
        auto right = ParseUnary();
        if (!right.ok()) return right.status();
        left = *left && *right;
      } else {
        break;
      }
    }
    return left;
  }

  // Parse unary (!)
  absl::StatusOr<bool> ParseUnary() {
    SkipWhitespace();
    if (pos_ < expr_.length() && expr_[pos_] == '!') {
      pos_++;
      auto operand = ParseUnary();
      if (!operand.ok()) return operand.status();
      return !*operand;
    }
    return ParsePrimary();
  }

  // Parse primary (identifier or parenthesized expression)
  absl::StatusOr<bool> ParsePrimary() {
    SkipWhitespace();
    if (pos_ >= expr_.length()) {
      return absl::InvalidArgumentError("Unexpected end of expression");
    }

    // Parenthesized expression
    if (expr_[pos_] == '(') {
      pos_++;
      auto result = ParseExpression();
      if (!result.ok()) return result.status();
      SkipWhitespace();
      if (pos_ >= expr_.length() || expr_[pos_] != ')') {
        return absl::InvalidArgumentError("Missing closing parenthesis");
      }
      pos_++;
      return result;
    }

    // Identifier
    if (std::isalpha(expr_[pos_]) || expr_[pos_] == '_') {
      size_t start = pos_;
      while (pos_ < expr_.length() &&
             (std::isalnum(expr_[pos_]) || expr_[pos_] == '_')) {
        pos_++;
      }
      std::string_view identifier = expr_.substr(start, pos_ - start);
      
      // Check if macro is defined
      auto it = defined_macros_.find(identifier);
      if (it != defined_macros_.end()) {
        return it->second;
      }
      // Undefined macro is considered false
      return false;
    }

    return absl::InvalidArgumentError(
        absl::StrCat("Unexpected character: ", expr_[pos_]));
  }

  std::string_view expr_;
  size_t pos_;
  const std::map<std::string_view, bool>& defined_macros_;
};

}  // namespace

absl::StatusOr<bool> EvaluatePreprocessorExpression(
    std::string_view expr,
    const std::map<std::string_view, bool>& defined_macros) {
  PreprocessorExpressionEvaluator evaluator(expr, defined_macros);
  return evaluator.Evaluate();
}

}  // namespace verilog

