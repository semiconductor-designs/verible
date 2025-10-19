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

#ifndef VERIBLE_VERILOG_ANALYSIS_VERILOG_ANALYZER_H_
#define VERIBLE_VERILOG_ANALYSIS_VERILOG_ANALYZER_H_

#include <cstddef>
#include <memory>
#include <optional>
#include <string_view>
#include <utility>

#include "absl/status/status.h"
#include "verible/common/analysis/file-analyzer.h"
#include "verible/common/strings/mem-block.h"
#include "verible/common/text/token-stream-view.h"
#include "verible/verilog/preprocessor/verilog-preprocess.h"

namespace verilog {

// VerilogAnalyzer analyzes Verilog and SystemVerilog code syntax.
class VerilogAnalyzer : public verible::FileAnalyzer {
 public:
  using FileOpener = VerilogPreprocess::FileOpener;

  VerilogAnalyzer(std::shared_ptr<verible::MemBlock> text,
                  std::string_view name,
                  const VerilogPreprocess::Config &preprocess_config,
                  FileOpener file_opener = nullptr)
      : verible::FileAnalyzer(std::move(text), name),
        preprocess_config_(preprocess_config),
        file_opener_(file_opener) {}

  // Legacy constructor.
  VerilogAnalyzer(std::string_view text, std::string_view name,
                  const VerilogPreprocess::Config &preprocess_config,
                  FileOpener file_opener = nullptr)
      : verible::FileAnalyzer(text, name),
        preprocess_config_(preprocess_config),
        file_opener_(file_opener) {}

  // Legacy constructor.
  // TODO(hzeller): Remove once every instantiation sets preprocessor config.
  VerilogAnalyzer(std::string_view text, std::string_view name)
      : VerilogAnalyzer(text, name, VerilogPreprocess::Config()) {}

  VerilogAnalyzer(const VerilogAnalyzer &) = delete;
  VerilogAnalyzer(VerilogAnalyzer &&) = delete;

  // Lex-es the input text into tokens.
  absl::Status Tokenize() final;

  // Create token stream view without comments and whitespace.
  // The retained tokens will become leaves of a concrete syntax tree.
  void FilterTokensForSyntaxTree();

  // Analyzes the syntax and structure of a source file (lex and parse).
  // Result of parsing is stored in syntax_tree_, which may contain gaps
  // if there are syntax errors.
  absl::Status Analyze();

  absl::Status LexStatus() const { return lex_status_; }

  absl::Status ParseStatus() const { return parse_status_; }

  size_t MaxUsedStackSize() const { return max_used_stack_size_; }

  // Automatically analyze with the correct parsing mode, as detected
  // by parser directive comments.
  static std::unique_ptr<VerilogAnalyzer> AnalyzeAutomaticMode(
      const std::shared_ptr<verible::MemBlock> &text, std::string_view name,
      const VerilogPreprocess::Config &preprocess_config);

  static std::unique_ptr<VerilogAnalyzer> AnalyzeAutomaticMode(
      std::string_view text, std::string_view name,
      const VerilogPreprocess::Config &preprocess_config);

  // Automatically analyze with correct parsing mode like AnalyzeAutomaticMode()
  // but attempt first with preprocessor disabled to get as complete as
  // possible parse tree; if this yields to syntax errors, fall back to
  // enabling preprocess branches.
  static std::unique_ptr<VerilogAnalyzer> AnalyzeAutomaticPreprocessFallback(
      std::string_view text, std::string_view name);

  const VerilogPreprocessData &PreprocessorData() const {
    return preprocessor_data_;
  }

  // Feature 2 (v5.4.0): Seed preprocessor with preloaded macros
  // Call this before Analyze() to make macros from pre-includes available
  void SetPreloadedMacros(
      const VerilogPreprocessData::MacroDefinitionRegistry& macros) {
    preloaded_macros_ = macros;
  }

  // Maybe this belongs in a subclass like VerilogFileAnalyzer?
  // TODO(fangism): Retain a copy of the token stream transformer because it
  // may contain tokens backed by generated text.

 protected:
  // Apply context-based disambiguation of tokens.
  void ContextualizeTokens();

  // Scan comments for parsing mode directives.
  // Returns a string that is first argument of the directive, e.g.:
  //     // verilog_syntax: mode-x
  // results in "mode-x".
  static std::string_view ScanParsingModeDirective(
      const verible::TokenSequence &raw_tokens);

  // Special string inside a comment that triggers setting parsing mode.
  static constexpr std::string_view kParseDirectiveName = "verilog_syntax:";

 private:
  // Attempt to parse all macro arguments as expressions.  Where parsing as an
  // expession succeeds, substitute the leaf with a node with the expression's
  // syntax tree.  If parsing fails, leave the MacroArg token unexpanded.
  void ExpandMacroCallArgExpressions();

  // Information about parser internals.

  // True if input text has already been lexed.
  bool tokenized_ = false;

  // Maximum symbol stack depth.
  size_t max_used_stack_size_ = 0;

  // Preprocessor.
  const VerilogPreprocess::Config preprocess_config_;
  FileOpener file_opener_;
  VerilogPreprocessData preprocessor_data_;

  // Feature 2 (v5.4.0): Preloaded macros from pre-include files
  std::optional<VerilogPreprocessData::MacroDefinitionRegistry> preloaded_macros_;

  // Status of lexing.
  absl::Status lex_status_;

  // Status of parsing.
  absl::Status parse_status_;
};

}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_VERILOG_ANALYZER_H_
