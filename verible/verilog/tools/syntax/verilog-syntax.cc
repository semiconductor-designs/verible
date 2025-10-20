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

// verilog_syntax is a simple command-line utility to check Verilog syntax
// for the given file.
//
// Example usage:
// verilog_syntax --verilog_trace_parser files...

#include <algorithm>
#include <chrono>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <memory>
#include <sstream>  // IWYU pragma: keep  // for ostringstream, istringstream
#include <string>   // for string, allocator, etc
#include <string_view>
#include <utility>
#include <vector>

#include "absl/flags/flag.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "nlohmann/json.hpp"
#include "verible/common/strings/mem-block.h"
#include "verible/common/text/concrete-syntax-tree.h"
#include "verible/common/text/parser-verifier.h"
#include "verible/common/text/text-structure.h"
#include "verible/common/text/token-info-json.h"
#include "verible/common/text/token-info.h"
#include "verible/common/util/enum-flags.h"
#include "verible/common/util/file-util.h"
#include "verible/common/util/init-command-line.h"
#include "verible/common/util/iterator-range.h"
#include "verible/common/util/logging.h"  // for operator<<, LOG, LogMessage, etc
#include "verible/verilog/CST/verilog-tree-json.h"
#include "verible/verilog/CST/verilog-tree-print.h"
#include "verible/verilog/analysis/include-file-resolver.h"
#include "verible/verilog/analysis/json-diagnostics.h"
#include "verible/verilog/analysis/package-context-resolver.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/analysis/verilog-excerpt-parse.h"
#include "verible/verilog/parser/verilog-parser.h"
#include "verible/verilog/parser/verilog-token-classifications.h"
#include "verible/verilog/parser/verilog-token-enum.h"
#include "verible/verilog/parser/verilog-token.h"
#include "verible/verilog/tools/syntax/file-index-tracker.h"  // v5.7.0

// Controls parser selection behavior
enum class LanguageMode {
  // May try multiple language options starting with SV, stops on first success.
  kAutoDetect,
  // Strict SystemVerilog 2017, no automatic trying of alternative parsing modes
  kSystemVerilog,
  // Verilog library map sub-language only.  LRM Chapter 33.
  kVerilogLibraryMap,
};

static const verible::EnumNameMap<LanguageMode> &LanguageModeStringMap() {
  static const verible::EnumNameMap<LanguageMode> kLanguageModeStringMap({
      {"auto", LanguageMode::kAutoDetect},
      {"sv", LanguageMode::kSystemVerilog},
      {"lib", LanguageMode::kVerilogLibraryMap},
  });
  return kLanguageModeStringMap;
}

static std::ostream &operator<<(std::ostream &stream, LanguageMode mode) {
  return LanguageModeStringMap().Unparse(mode, stream);
}

static bool AbslParseFlag(std::string_view text, LanguageMode *mode,
                          std::string *error) {
  return LanguageModeStringMap().Parse(text, mode, error, "--flag value");
}

static std::string AbslUnparseFlag(const LanguageMode &mode) {
  std::ostringstream stream;
  stream << mode;
  return stream.str();
}

ABSL_FLAG(
    LanguageMode, lang, LanguageMode::kAutoDetect,  //
    "Selects language variant to parse.  Options:\n"
    "  auto: SystemVerilog-2017, but may auto-detect alternate parsing modes\n"
    "  sv: strict SystemVerilog-2017, with explicit alternate parsing modes\n"
    "  lib: Verilog library map language (LRM Ch. 33)\n");

ABSL_FLAG(
    bool, export_json, false,
    "Uses JSON for output. Intended to be used as an input for other tools.");

// v5.7.0: VeriPG enhancements - file index tracking and error recovery
ABSL_FLAG(bool, export_indexed_json, false,
          "v5.7.0: Export JSON with file index mapping for multi-file batch processing.\n"
          "Includes 'file_index' mapping <indexed> placeholders to actual paths.\n"
          "Output format: {\"file_index\": {\"0\": \"/path/file1.sv\", ...}, \"cst\": {...}}.\n"
          "This is an alternative to --export_json with additional file tracking.\n"
          "Mutually exclusive with --export_json.");

ABSL_FLAG(bool, continue_on_error, false,
          "v5.7.0: Continue processing remaining files even if some fail to parse.\n"
          "Useful for batch processing large repositories (e.g., OpenTitan: 3,659 files).\n"
          "Exit code: 1 if any errors occurred, 0 if all succeeded.\n"
          "Works with both --export_json and --export_indexed_json.");

ABSL_FLAG(bool, printtree, false, "Whether or not to print the tree");
ABSL_FLAG(bool, printtokens, false, "Prints all lexed and filtered tokens");
ABSL_FLAG(bool, printrawtokens, false,
          "Prints all lexed tokens, including filtered ones.");
ABSL_FLAG(int, error_limit, 0,
          "Limit the number of syntax errors reported.  "
          "(0: unlimited)");
ABSL_FLAG(
    bool, verifytree, false,
    "Verifies that all tokens are parsed into tree, prints unmatched tokens");

ABSL_FLAG(bool, show_diagnostic_context, false,
          "prints an additional "
          "line on which the diagnostic was found,"
          "followed by a line with a position marker");

ABSL_FLAG(std::vector<std::string>, include_paths, {},
          "Comma-separated list of directories to search for `include files.\n"
          "Example: --include_paths=/path/to/includes,/other/path");

ABSL_FLAG(bool, preprocess, true,
          "Enable preprocessing (include file resolution).\n"
          "Set to false for syntax-only checking without preprocessing.");

ABSL_FLAG(bool, expand_macros, false,
          "Enable macro expansion during preprocessing.\n"
          "Default is false to preserve macros for knowledge graph building.\n"
          "Set to true if you want to see expanded macro bodies.");

ABSL_FLAG(bool, inject_macro_markers, false,
          "v5.6.0: Inject macro boundary markers for context preservation.\n"
          "Experimental feature for improved context tracking across macro expansions.\n"
          "Only active when expand_macros=true. Default is false.");

ABSL_FLAG(std::string, arrow_disambiguation_mode, "macro_aware",
          "v5.6.0 Week 7-8: Arrow operator disambiguation strategy.\n"
          "Options: 'macro_aware' (use macro markers), 'enhanced_heuristic' (multi-token lookahead), 'both' (A/B test).\n"
          "Default is 'macro_aware' which preserves context across macros.");

ABSL_FLAG(std::vector<std::string>, pre_include, {},
          "List of files to include before parsing the main file.\n"
          "These files are processed first, making their macros available.\n"
          "Useful for UVM/OpenTitan testbenches that require macro preludes.\n"
          "Example: --pre_include=uvm_macros.svh,dv_macros.svh");

ABSL_FLAG(std::vector<std::string>, package_context, {},
          "List of package files to parse for context (macros, types).\n"
          "Package files are parsed first, making their definitions available.\n"
          "Useful for OpenTitan UVM testbenches that rely on package context.\n"
          "Example: --package_context=dv_base_test_pkg.sv");

ABSL_FLAG(bool, package_context_disable_includes, false,
          "Disable include processing in package context files.\n"
          "Use this if package includes cause parsing issues.\n"
          "Macros from the package file itself will still be extracted.");

ABSL_FLAG(bool, auto_wrap_includes, false,
          "Automatically wrap include snippets in a module context.\n"
          "Useful for parsing standalone include files (e.g., tb__xbar_connect.sv)\n"
          "that are meant to be included within a larger module.\n"
          "When enabled, wraps the file content in a generated module with common signals.");

ABSL_FLAG(std::string, macro_library, "",
          "Path to a macro library file with predefined macros.\n"
          "Format: MACRO_NAME(args)=definition (one per line, # for comments).\n"
          "Useful for loading common DV/UVM macros without full file includes.\n"
          "Example: --macro_library=opentitan_dv.macros");

ABSL_FLAG(bool, show_stats, false,
          "Show parse statistics at program exit.\n"
          "Includes success/failure rates, arrow token disambiguation counts,\n"
          "parse timing, and error patterns.");

// Parse statistics tracking structure
struct ParseStats {
  int total_files = 0;
  int successful_parses = 0;
  int failed_parses = 0;
  int arrow_tokens_processed = 0;
  int arrow_as_trigger = 0;
  int arrow_as_logical_implies = 0;
  std::map<std::string, int> error_patterns;
  std::chrono::milliseconds total_parse_time{0};
  
  void RecordSuccess() {
    total_files++;
    successful_parses++;
  }
  
  void RecordFailure(const std::string& error_msg) {
    total_files++;
    failed_parses++;
    
    // Categorize error patterns
    if (error_msg.find("syntax error at token \"->\"") != std::string::npos) {
      error_patterns["arrow_syntax_error"]++;
    } else if (error_msg.find("syntax error") != std::string::npos) {
      error_patterns["general_syntax_error"]++;
    } else if (error_msg.find("Include file not found") != std::string::npos) {
      error_patterns["include_not_found"]++;
    } else if (error_msg.find("macro") != std::string::npos) {
      error_patterns["macro_error"]++;
    } else {
      error_patterns["other_error"]++;
    }
  }
  
  void RecordParseTime(std::chrono::milliseconds duration) {
    total_parse_time += duration;
  }
  
  void PrintReport() const {
    std::cout << "\n=== Parse Statistics ===" << std::endl;
    std::cout << "Total files: " << total_files << std::endl;
    if (total_files > 0) {
      std::cout << "Successful: " << successful_parses 
                << " (" << std::fixed << std::setprecision(1)
                << (100.0 * successful_parses / total_files) << "%)" << std::endl;
      std::cout << "Failed: " << failed_parses 
                << " (" << std::fixed << std::setprecision(1)
                << (100.0 * failed_parses / total_files) << "%)" << std::endl;
      
      if (arrow_tokens_processed > 0) {
        std::cout << "\nArrow token (->) disambiguation:" << std::endl;
        std::cout << "  Total processed: " << arrow_tokens_processed << std::endl;
        std::cout << "  As trigger: " << arrow_as_trigger 
                  << " (" << std::fixed << std::setprecision(1)
                  << (100.0 * arrow_as_trigger / arrow_tokens_processed) << "%)" << std::endl;
        std::cout << "  As logical implies: " << arrow_as_logical_implies 
                  << " (" << std::fixed << std::setprecision(1)
                  << (100.0 * arrow_as_logical_implies / arrow_tokens_processed) << "%)" << std::endl;
      }
      
      std::cout << "\nParse timing:" << std::endl;
      std::cout << "  Total: " << total_parse_time.count() << "ms" << std::endl;
      std::cout << "  Average: " << (total_parse_time.count() / total_files) << "ms per file" << std::endl;
      
      if (!error_patterns.empty()) {
        std::cout << "\nError patterns:" << std::endl;
        for (const auto& [pattern, count] : error_patterns) {
          std::cout << "  " << pattern << ": " << count << std::endl;
        }
      }
    }
    std::cout << "========================\n" << std::endl;
  }
};

static ParseStats global_stats;

using nlohmann::json;
using verible::ConcreteSyntaxTree;
using verible::ParserVerifier;
using verible::TextStructureView;
using verilog::VerilogAnalyzer;

// Helper function to wrap content in a module for auto-wrap mode
static std::shared_ptr<verible::MemBlock> WrapContentInModule(
    const std::shared_ptr<verible::MemBlock> &original_content) {
  std::string wrapped;
  wrapped += "// Auto-generated wrapper for include snippet\n";
  wrapped += "module __verible_auto_wrapper;\n";
  wrapped += "  // Common signals for testbenches\n";
  wrapped += "  wire clk, rst_n, clk_i, rst_ni;\n";
  wrapped += "  wire clk_main, clk_peri, clk_dbg, clk_mbx;\n";
  wrapped += "\n";
  wrapped += "  // Original content\n";
  wrapped += original_content->AsStringView();
  wrapped += "\n";
  wrapped += "endmodule\n";
  
  return std::make_shared<verible::StringMemBlock>(std::move(wrapped));
}

// Helper function to load macro library file and convert to `define statements
static absl::StatusOr<std::string> LoadMacroLibrary(std::string_view library_path) {
  // Read the library file
  auto content_or = verible::file::GetContentAsString(std::string(library_path));
  if (!content_or.ok()) {
    return absl::NotFoundError(
        absl::StrCat("Macro library file not found: ", library_path));
  }
  
  std::string content = *content_or;
  std::string defines;
  
  // Parse line by line
  std::istringstream stream(content);
  std::string line;
  int line_number = 0;
  
  while (std::getline(stream, line)) {
    line_number++;
    
    // Trim whitespace
    size_t start = line.find_first_not_of(" \t");
    if (start == std::string::npos) continue;  // Empty line
    line = line.substr(start);
    
    // Skip comments
    if (line.empty() || line[0] == '#') continue;
    
    // Parse format: MACRO_NAME(args)=definition or MACRO_NAME=definition
    size_t eq_pos = line.find('=');
    if (eq_pos == std::string::npos) {
      return absl::InvalidArgumentError(
          absl::StrCat("Invalid macro definition at line ", line_number, 
                       ": missing '=' in: ", line));
    }
    
    std::string macro_call = line.substr(0, eq_pos);
    std::string definition = line.substr(eq_pos + 1);
    
    // Trim spaces around macro call and definition
    size_t end = macro_call.find_last_not_of(" \t");
    if (end != std::string::npos) {
      macro_call = macro_call.substr(0, end + 1);
    }
    
    start = definition.find_first_not_of(" \t");
    if (start != std::string::npos) {
      definition = definition.substr(start);
    }
    
    // Convert to SystemVerilog `define
    defines += "`define " + macro_call + " " + definition + "\n";
  }
  
  return defines;
}

static std::unique_ptr<VerilogAnalyzer> ParseWithLanguageMode(
    const std::shared_ptr<verible::MemBlock> &content,
    std::string_view filename,
    const verilog::VerilogPreprocess::Config &preprocess_config,
    VerilogAnalyzer::FileOpener file_opener = nullptr,
    const verilog::VerilogPreprocessData* preloaded_data = nullptr,
    verilog::LexicalContext::DisambiguationMode arrow_mode = 
        verilog::LexicalContext::DisambiguationMode::kMacroAware) {
  switch (absl::GetFlag(FLAGS_lang)) {
    case LanguageMode::kAutoDetect: {
      // Feature 2 (v5.4.0): If we have preloaded data, use explicit SV mode
      // because auto-detect doesn't support macro seeding yet
      if (preloaded_data) {
        auto analyzer = std::make_unique<VerilogAnalyzer>(content, filename,
                                                          preprocess_config,
                                                          file_opener);
        analyzer->SetPreloadedMacros(preloaded_data->macro_definitions);
        // v5.6.0 Week 7-8: Set disambiguation mode
        analyzer->SetArrowDisambiguationMode(arrow_mode);
        const auto status = ABSL_DIE_IF_NULL(analyzer)->Analyze();
        if (!status.ok()) std::cerr << status.message() << std::endl;
        return analyzer;
      }
      return VerilogAnalyzer::AnalyzeAutomaticMode(content, filename,
                                                   preprocess_config);
    }
    case LanguageMode::kSystemVerilog: {
      auto analyzer = std::make_unique<VerilogAnalyzer>(content, filename,
                                                        preprocess_config,
                                                        file_opener);
      // Feature 2 (v5.4.0): Seed with preloaded macros
      if (preloaded_data) {
        analyzer->SetPreloadedMacros(preloaded_data->macro_definitions);
      }
      // v5.6.0 Week 7-8: Set disambiguation mode
      analyzer->SetArrowDisambiguationMode(arrow_mode);
      const auto status = ABSL_DIE_IF_NULL(analyzer)->Analyze();
      if (!status.ok()) std::cerr << status.message() << std::endl;
      return analyzer;
    }
    case LanguageMode::kVerilogLibraryMap:
      return verilog::AnalyzeVerilogLibraryMap(content->AsStringView(),
                                               filename, preprocess_config);
      // TODO: AnalyzeVerilogLibraryMap doesn't support file_opener yet
  }
  return nullptr;
}

// Prints all tokens in view that are not matched in root.
static void VerifyParseTree(const TextStructureView &text_structure) {
  const ConcreteSyntaxTree &root = text_structure.SyntaxTree();
  if (root == nullptr) return;
  // TODO(fangism): this seems like a good method for TextStructureView.
  ParserVerifier verifier(*root, text_structure.GetTokenStreamView());
  auto unmatched = verifier.Verify();

  if (unmatched.empty()) {
    std::cout << std::endl << "All tokens matched." << std::endl;
  } else {
    std::cout << std::endl << "Unmatched Tokens:" << std::endl;
    for (const auto &token : unmatched) {
      std::cout << token << std::endl;
    }
  }
}

static bool ShouldIncludeTokenText(const verible::TokenInfo &token) {
  const verilog_tokentype tokentype =
      static_cast<verilog_tokentype>(token.token_enum());
  std::string_view type_str = verilog::TokenTypeToString(tokentype);
  // Don't include token's text for operators, keywords, or anything that is a
  // part of Verilog syntax. For such types, TokenTypeToString() is equal to
  // token's text. Exception has to be made for identifiers, because things like
  // "PP_Identifier" or "SymbolIdentifier" (which are values returned by
  // TokenTypeToString()) could be used as Verilog identifier.
  return verilog::IsIdentifierLike(tokentype) || (token.text() != type_str);
}

static int AnalyzeOneFile(
    const std::shared_ptr<verible::MemBlock> &content,
    std::string_view filename,
    const verilog::VerilogPreprocess::Config &preprocess_config,
    VerilogAnalyzer::FileOpener file_opener,
    const verilog::VerilogPreprocessData* preloaded_data,
    verilog::LexicalContext::DisambiguationMode arrow_mode,
    json *json_out) {
  int exit_status = 0;
  
  // Start timing
  auto start_time = std::chrono::high_resolution_clock::now();
  
  const auto analyzer =
      ParseWithLanguageMode(content, filename, preprocess_config, file_opener, preloaded_data, arrow_mode);
  const auto lex_status = ABSL_DIE_IF_NULL(analyzer)->LexStatus();
  const auto parse_status = analyzer->ParseStatus();

  // Record parse time
  auto end_time = std::chrono::high_resolution_clock::now();
  auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time);
  global_stats.RecordParseTime(duration);
  
  // Log slow parses
  if (duration.count() > 1000) {
    LOG(WARNING) << "Slow parse: " << filename << " took " << duration.count() << "ms";
  }

  if (!lex_status.ok() || !parse_status.ok()) {
    const std::vector<std::string> syntax_error_messages(
        analyzer->LinterTokenErrorMessages(
            absl::GetFlag(FLAGS_show_diagnostic_context)));
    const int error_limit = absl::GetFlag(FLAGS_error_limit);
    int error_count = 0;
    
    // Record failure with error message for pattern detection
    std::string first_error;
    if (!absl::GetFlag(FLAGS_export_json)) {
      const std::vector<std::string> syntax_error_messages(
          analyzer->LinterTokenErrorMessages(
              absl::GetFlag(FLAGS_show_diagnostic_context)));
      for (const auto &message : syntax_error_messages) {
        if (first_error.empty()) first_error = message;
        std::cout << message << std::endl;
        ++error_count;
        if (error_limit != 0 && error_count >= error_limit) break;
      }
    } else {
      (*json_out)["errors"] =
          verilog::GetLinterTokenErrorsAsJson(analyzer.get(), error_limit);
      if (!syntax_error_messages.empty()) {
        first_error = syntax_error_messages[0];
      }
    }
    
    global_stats.RecordFailure(first_error);
    exit_status = 1;
  } else {
    // Record success
    global_stats.RecordSuccess();
  }
  const bool parse_ok = parse_status.ok();

  std::function<void(std::ostream &, int)> token_translator;
  if (!absl::GetFlag(FLAGS_export_json)) {
    token_translator = [](std::ostream &stream, int e) {
      stream << verilog::verilog_symbol_name(e);
    };
  } else {
    token_translator = [](std::ostream &stream, int e) {
      stream << verilog::TokenTypeToString(static_cast<verilog_tokentype>(e));
    };
  }
  const verible::TokenInfo::Context context(analyzer->Data().Contents(),
                                            token_translator);
  // Check for printtokens flag, print all filtered tokens if on.
  if (absl::GetFlag(FLAGS_printtokens)) {
    if (!absl::GetFlag(FLAGS_export_json)) {
      std::cout << std::endl << "Lexed and filtered tokens:" << std::endl;
      for (const auto &t : analyzer->Data().GetTokenStreamView()) {
        t->ToStream(std::cout, context) << std::endl;
      }
    } else {
      json &tokens = (*json_out)["tokens"] = json::array();
      const auto &token_stream = analyzer->Data().GetTokenStreamView();
      for (const auto &t : token_stream) {
        tokens.push_back(
            verible::ToJson(*t, context, ShouldIncludeTokenText(*t)));
      }
    }
  }

  // Check for printrawtokens flag, print all tokens if on.
  if (absl::GetFlag(FLAGS_printrawtokens)) {
    if (!absl::GetFlag(FLAGS_export_json)) {
      std::cout << std::endl << "All lexed tokens:" << std::endl;
      for (const auto &t : analyzer->Data().TokenStream()) {
        t.ToStream(std::cout, context) << std::endl;
      }
    } else {
      json &tokens = (*json_out)["rawtokens"] = json::array();
      const auto &token_stream = analyzer->Data().TokenStream();
      for (const auto &t : token_stream) {
        tokens.push_back(
            verible::ToJson(t, context, ShouldIncludeTokenText(t)));
      }
    }
  }

  const auto &text_structure = analyzer->Data();
  const auto &syntax_tree = text_structure.SyntaxTree();

  // check for printtree flag, and print tree if on
  if (absl::GetFlag(FLAGS_printtree) && syntax_tree != nullptr) {
    if (!absl::GetFlag(FLAGS_export_json)) {
      std::cout << std::endl
                << "Parse Tree"
                << (!parse_ok ? " (incomplete due to syntax errors):" : ":")
                << std::endl;
      verilog::PrettyPrintVerilogTree(*syntax_tree, analyzer->Data().Contents(),
                                      &std::cout);
    } else {
      (*json_out)["tree"] = verilog::ConvertVerilogTreeToJson(
          *syntax_tree, analyzer->Data().Contents());
    }
  }

  // Check for verifytree, verify tree and print unmatched if on.
  if (absl::GetFlag(FLAGS_verifytree)) {
    if (!parse_ok) {
      std::cout << std::endl
                << "Note: verifytree will fail because syntax errors caused "
                   "sections of text to be dropped during error-recovery."
                << std::endl;
    }
    VerifyParseTree(text_structure);
  }

  return exit_status;
}

int main(int argc, char **argv) {
  const auto usage =
      absl::StrCat("usage: ", argv[0], " [options] <file> [<file>...]");
  const auto args = verible::InitCommandLine(usage, &argc, &argv);

  // v5.7.0: Validate mutually exclusive flags
  if (absl::GetFlag(FLAGS_export_json) && 
      absl::GetFlag(FLAGS_export_indexed_json)) {
    std::cerr << "Error: --export_json and --export_indexed_json are mutually exclusive.\n"
              << "Use --export_json for standard output (v5.6.0 compatible), or\n"
              << "    --export_indexed_json for indexed output with file_index mapping (v5.7.0)."
              << std::endl;
    return 1;
  }

  json json_out;

  // Create include file resolver if paths provided
  const auto include_paths = absl::GetFlag(FLAGS_include_paths);
  const bool enable_preprocessing = absl::GetFlag(FLAGS_preprocess);
  
  std::unique_ptr<verilog::IncludeFileResolver> include_resolver;
  if (!include_paths.empty() && enable_preprocessing) {
    include_resolver = std::make_unique<verilog::IncludeFileResolver>(include_paths);
    std::cerr << "Include file support enabled with " << include_paths.size() 
              << " search path(s)" << std::endl;
  }

  // Process pre-include files if specified
  const auto pre_includes = absl::GetFlag(FLAGS_pre_include);
  if (!pre_includes.empty()) {
    if (!include_resolver) {
      std::cerr << "Error: --pre_include requires --include_paths to be set" << std::endl;
      return 1;
    }
    
    std::cerr << "Processing " << pre_includes.size() << " pre-include file(s)..." << std::endl;
    auto status = include_resolver->PreloadIncludes(pre_includes);
    if (!status.ok()) {
      std::cerr << "Error processing pre-includes: " << status.message() << std::endl;
      return 1;
    }
    
    // Show which macros were preloaded
    const auto* preloaded_data = include_resolver->GetPreloadedData();
    if (preloaded_data) {
      std::cerr << "Preloaded " << preloaded_data->macro_definitions.size() 
                << " macro(s) from pre-include files" << std::endl;
    }
  }

  // v5.6.0 Week 7-8: Parse arrow disambiguation mode
  const std::string mode_str = absl::GetFlag(FLAGS_arrow_disambiguation_mode);
  verilog::LexicalContext::DisambiguationMode arrow_mode = 
      verilog::LexicalContext::DisambiguationMode::kMacroAware;
  
  if (mode_str == "enhanced_heuristic") {
    arrow_mode = verilog::LexicalContext::DisambiguationMode::kEnhancedHeuristic;
    std::cerr << "Using enhanced heuristic mode for arrow disambiguation" << std::endl;
  } else if (mode_str == "both") {
    arrow_mode = verilog::LexicalContext::DisambiguationMode::kBoth;
    std::cerr << "Using A/B testing mode (comparing both strategies)" << std::endl;
  } else if (mode_str != "macro_aware") {
    std::cerr << "Warning: Unknown arrow_disambiguation_mode '" << mode_str 
              << "', defaulting to 'macro_aware'" << std::endl;
  }

  // Feature 3 (v5.4.0): Process package context files if specified
  std::unique_ptr<verilog::CombinedPackageContext> package_context;
  const auto package_files = absl::GetFlag(FLAGS_package_context);
  if (!package_files.empty()) {
    const bool disable_includes = absl::GetFlag(FLAGS_package_context_disable_includes);
    std::cerr << "Processing " << package_files.size() << " package file(s) for context";
    if (disable_includes) {
      std::cerr << " (includes disabled)";
    }
    std::cerr << "..." << std::endl;
    
    // Create package context resolver with include option
    verilog::PackageContextResolver pkg_resolver(include_resolver.get(), !disable_includes);
    
    auto context_or = pkg_resolver.ParsePackages(package_files);
    if (!context_or.ok()) {
      std::cerr << "Error processing package context: " << context_or.status().message() << std::endl;
      return 1;
    }
    
    package_context = std::make_unique<verilog::CombinedPackageContext>(std::move(*context_or));
    std::cerr << "Loaded package context: " 
              << package_context->MacroCount() << " macro(s), "
              << package_context->TypeCount() << " type(s)" << std::endl;
  }

  int exit_status = 0;
  // All positional arguments are file names.  Exclude program name.
  for (std::string_view filename :
       verible::make_range(args.begin() + 1, args.end())) {
    auto content_status = verible::file::GetContentAsMemBlock(filename);
    if (!content_status.status().ok()) {
      std::cerr << content_status.status().message() << std::endl;
      exit_status = 1;
      continue;
    }
    std::shared_ptr<verible::MemBlock> content = std::move(*content_status);

    // Feature 3 (v5.4.1): Auto-wrap include snippets if flag is set
    const bool auto_wrap = absl::GetFlag(FLAGS_auto_wrap_includes);
    if (auto_wrap) {
      content = WrapContentInModule(content);
    }

    // Feature 4 (v5.4.1): Prepend macro library definitions if flag is set
    const std::string macro_library_path = absl::GetFlag(FLAGS_macro_library);
    if (!macro_library_path.empty()) {
      auto defines_or = LoadMacroLibrary(macro_library_path);
      if (!defines_or.ok()) {
        std::cerr << "Error loading macro library: " << defines_or.status().message() << std::endl;
        exit_status = 1;
        continue;
      }
      
      // Prepend macro definitions to content
      std::string combined_content = *defines_or;
      combined_content += "\n";
      combined_content += content->AsStringView();
      content = std::make_shared<verible::StringMemBlock>(std::move(combined_content));
    }

    // Configure preprocessing based on flags
    // expand_macros can work standalone or with include_files
    // include_files requires include_resolver (for resolving paths)
    const bool should_expand_macros = absl::GetFlag(FLAGS_expand_macros);
    const bool should_inject_markers = absl::GetFlag(FLAGS_inject_macro_markers);
    const verilog::VerilogPreprocess::Config preprocess_config{
        .filter_branches = true,
        .include_files = enable_preprocessing && include_resolver != nullptr,
        .expand_macros = should_expand_macros,  // Controlled by --expand_macros flag (default: false)
        .inject_macro_markers = should_inject_markers && should_expand_macros,  // v5.6.0: Only when expanding
    };
    
    // Create file_opener lambda if include resolver available
    VerilogAnalyzer::FileOpener file_opener = nullptr;
    if (include_resolver) {
      file_opener = [&include_resolver, &filename](std::string_view include_file) 
          -> absl::StatusOr<std::string_view> {
        return include_resolver->ResolveInclude(include_file, filename);
      };
    }
    
    // Get preloaded macros from pre-includes
    const auto* preloaded_data = include_resolver ? include_resolver->GetPreloadedData() : nullptr;
    
    // Feature 3 (v5.4.0): Merge package context macros with preloaded data
    // Note: We only merge macro_definitions, not the entire VerilogPreprocessData
    verilog::VerilogPreprocessData combined_preload_data;
    if (preloaded_data) {
      // Copy only macro definitions
      for (const auto& [name, definition] : preloaded_data->macro_definitions) {
        combined_preload_data.macro_definitions.insert({name, definition});
      }
    }
    if (package_context) {
      // Add package context macros (package macros take precedence)
      for (const auto& [name, definition] : package_context->all_macros) {
        auto it = combined_preload_data.macro_definitions.find(name);
        if (it != combined_preload_data.macro_definitions.end()) {
          combined_preload_data.macro_definitions.erase(it);
        }
        combined_preload_data.macro_definitions.insert({name, definition});
      }
    }
    const auto* final_preload_data = (preloaded_data || package_context) ? &combined_preload_data : nullptr;
    
    json file_json;
    int file_status =
        AnalyzeOneFile(content, filename, preprocess_config, file_opener, final_preload_data, arrow_mode, &file_json);
    exit_status = std::max(exit_status, file_status);
    if (absl::GetFlag(FLAGS_export_json)) {
      json_out[std::string{filename.begin(), filename.end()}] =
          std::move(file_json);
    }
  }

  if (absl::GetFlag(FLAGS_export_json)) {
    std::cout << std::setw(2) << json_out << std::endl;
  }

  // Print statistics if requested
  if (absl::GetFlag(FLAGS_show_stats)) {
    global_stats.PrintReport();
  }

  return exit_status;
}
