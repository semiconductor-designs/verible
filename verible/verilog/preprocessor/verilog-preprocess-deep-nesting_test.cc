// Copyright 2025
// Deep Nesting Fix - TDD Red Phase Test

#include "verible/verilog/preprocessor/verilog-preprocess.h"

#include <string>
#include <string_view>

#include "absl/status/statusor.h"
#include "gtest/gtest.h"
#include "verible/common/text/token-stream-view.h"
#include "verible/verilog/parser/verilog-lexer.h"
#include "verible/verilog/parser/verilog-token-enum.h"

namespace verilog {
namespace {

using verible::TokenStreamView;
using verible::InitTokenStreamView;

// Helper: Simple lexer wrapper (copied from verilog-preprocess_test.cc)
class LexerTester {
 public:
  explicit LexerTester(std::string_view text) : lexer_(text) {
    for (lexer_.DoNextToken(); !lexer_.GetLastToken().isEOF();
         lexer_.DoNextToken()) {
      lexed_sequence_.push_back(lexer_.GetLastToken());
    }
    InitTokenStreamView(lexed_sequence_, &stream_view_);
  }

  TokenStreamView GetTokenStreamView() const { return stream_view_; }

 private:
  VerilogLexer lexer_;
  verible::TokenSequence lexed_sequence_;
  TokenStreamView stream_view_;
};

// Test 1: Basic 3-level nesting
TEST(DeepNestingTest, ThreeLevelNesting) {
  // Simulate 3 files:
  // level3.svh: `define LEVEL3 3
  // level2.svh: `include "level3.svh" \n `define LEVEL2 2
  // test.sv: `include "level2.svh" \n module test; int x = `LEVEL3; endmodule

  const std::string_view level3_content = "`define LEVEL3 3\n";
  const std::string_view level2_content = "`include \"level3.svh\"\n`define LEVEL2 2\n";  // Level2 includes level3!

  // FileOpener that returns level3 when asked for level2's include
  VerilogPreprocess::FileOpener file_opener =
      [&](std::string_view filename) -> absl::StatusOr<std::string_view> {
    if (filename == "level3.svh") return level3_content;
    if (filename == "level2.svh") return level2_content;
    return absl::NotFoundError("File not found");
  };

  // Main source: includes level2.svh (which includes level3.svh)
  const std::string main_src = "`include \"level2.svh\"\nmodule test; int x = `LEVEL3; endmodule\n";

  VerilogPreprocess::Config config{
      .filter_branches = true,
      .include_files = true,
      .expand_macros = true,
  };

  VerilogPreprocess preprocessor(config, file_opener);
  LexerTester lexer(main_src);
  const auto preprocessed_data = preprocessor.ScanStream(lexer.GetTokenStreamView());

  // Check: no errors
  EXPECT_TRUE(preprocessed_data.errors.empty()) 
      << "Errors: " << (preprocessed_data.errors.empty() ? "none" : preprocessed_data.errors[0].error_message);

  // Check: preprocessed stream is not empty
  EXPECT_FALSE(preprocessed_data.preprocessed_token_stream.empty()) 
      << "Preprocessed token stream should not be empty";

  // Check: LEVEL3 macro was defined (propagated from level3 through level2 to main)
  EXPECT_TRUE(preprocessed_data.macro_definitions.find("LEVEL3") != 
              preprocessed_data.macro_definitions.end())
      << "LEVEL3 macro should be defined after deep nesting";

  // Check: LEVEL2 macro was also defined
  EXPECT_TRUE(preprocessed_data.macro_definitions.find("LEVEL2") != 
              preprocessed_data.macro_definitions.end())
      << "LEVEL2 macro should be defined";
}

// Test 2: 4-level nesting
TEST(DeepNestingTest, FourLevelNesting) {
  const std::string_view level4_content = "`define LEVEL4 4\n";
  const std::string_view level3_content = "`include \"level4.svh\"\n`define LEVEL3 3\n";  // level3 includes level4
  const std::string_view level2_content = "`include \"level3.svh\"\n`define LEVEL2 2\n";  // level2 includes level3

  VerilogPreprocess::FileOpener file_opener =
      [&](std::string_view filename) -> absl::StatusOr<std::string_view> {
    if (filename == "level4.svh") return level4_content;
    if (filename == "level3.svh") return level3_content;
    if (filename == "level2.svh") return level2_content;
    return absl::NotFoundError("File not found");
  };

  const std::string main_src = "`include \"level2.svh\"\nmodule test; int x = `LEVEL4; endmodule\n";

  VerilogPreprocess::Config config{
      .filter_branches = true,
      .include_files = true,
      .expand_macros = true,
  };

  VerilogPreprocess preprocessor(config, file_opener);
  LexerTester lexer(main_src);
  const auto preprocessed_data = preprocessor.ScanStream(lexer.GetTokenStreamView());

  EXPECT_TRUE(preprocessed_data.errors.empty());
  EXPECT_FALSE(preprocessed_data.preprocessed_token_stream.empty());
  EXPECT_TRUE(preprocessed_data.macro_definitions.find("LEVEL4") != 
              preprocessed_data.macro_definitions.end());
}

}  // namespace
}  // namespace verilog

