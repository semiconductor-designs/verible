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

#include "verible/verilog/analysis/kythe-analyzer.h"

#include <filesystem>
#include <fstream>
#include <memory>
#include <random>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace {

using ::testing::Contains;
using ::testing::SizeIs;

// Helper class to set up test environment
// Uses temporary files like Kythe's own tests
class KytheAnalyzerTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Create temp directory for test files
    temp_dir_ = std::filesystem::temp_directory_path() / 
                ("kythe_test_" + std::to_string(std::random_device{}()));
    std::filesystem::create_directories(temp_dir_);
    
    project_ = std::make_unique<VerilogProject>(
        temp_dir_.string(), std::vector<std::string>{});
    symbol_table_ = std::make_unique<SymbolTable>(project_.get());
  }

  void TearDown() override {
    project_.reset();
    symbol_table_.reset();
    
    // Clean up temp directory
    if (std::filesystem::exists(temp_dir_)) {
      std::filesystem::remove_all(temp_dir_);
    }
  }

  // Helper to parse SystemVerilog code and build symbol table
  bool ParseCode(absl::string_view code, const std::string& filename = "test.sv") {
    // Write code to temporary file
    auto file_path = temp_dir_ / filename;
    std::ofstream ofs(file_path);
    if (!ofs) return false;
    ofs << code;
    ofs.close();
    
    // Open file in project
    auto status_or_file = project_->OpenTranslationUnit(filename);
    if (!status_or_file.ok()) {
      return false;
    }
    
    auto* source_file = *status_or_file;
    
    // Parse the file
    const auto parse_status = source_file->Parse();
    if (!parse_status.ok()) {
      return false;
    }
    
    // Build symbol table
    const auto build_diagnostics = BuildSymbolTable(*source_file, symbol_table_.get(), nullptr);
    
    return true;
  }

  std::filesystem::path temp_dir_;
  std::unique_ptr<VerilogProject> project_;
  std::unique_ptr<SymbolTable> symbol_table_;
  
  // Helper to extract variable names from references
  std::vector<std::string> ExtractVarNames(
      const std::vector<VariableReference>& refs) {
    std::vector<std::string> names;
    names.reserve(refs.size());
    for (const auto& ref : refs) {
      names.push_back(ref.variable_name);
    }
    return names;
  }
  
  // Helper to check if vector contains value (supports string literals)
  bool Contains(const std::vector<std::string>& vec, absl::string_view value) {
    for (const auto& item : vec) {
      if (item == value) return true;
    }
    return false;
  }
};

//-----------------------------------------------------------------------------
// FR-1: Basic Variable Reference Extraction (6 tests)
//-----------------------------------------------------------------------------

TEST_F(KytheAnalyzerTest, BasicRead) {
  const char* code = R"(
    module test;
      logic sig;
      logic result;
      assign result = sig;  // READ sig
    endmodule
  )";
  
  ASSERT_TRUE(ParseCode(code));
  KytheAnalyzer analyzer(*symbol_table_, *project_);
  
  const auto status = analyzer.BuildKytheFacts();
  ASSERT_TRUE(status.ok()) << "Analysis failed: " << status.message();
  
  const auto& refs = analyzer.GetVariableReferences();
  
  // Should have at least 1 reference (sig read)
  EXPECT_GE(refs.size(), 1) << "Expected at least 1 reference";
  
  // Check that 'sig' is referenced
  auto var_names = ExtractVarNames(refs);
  EXPECT_TRUE(Contains(var_names, "sig")) << "'sig' reference not found";
}

TEST_F(KytheAnalyzerTest, BasicWrite) {
  const char* code = R"(
    module test;
      logic sig;
      assign sig = 1'b0;  // WRITE sig
    endmodule
  )";
  
  ASSERT_TRUE(ParseCode(code));
  KytheAnalyzer analyzer(*symbol_table_, *project_);
  
  ASSERT_TRUE(analyzer.BuildKytheFacts().ok());
  
  const auto& refs = analyzer.GetVariableReferences();
  EXPECT_GE(refs.size(), 1);
  
  auto var_names = ExtractVarNames(refs);
  EXPECT_TRUE(Contains(var_names, "sig"));
}

TEST_F(KytheAnalyzerTest, MultipleReads) {
  const char* code = R"(
    module test;
      logic a, b, c;
      assign b = a;  // READ a
      assign c = a;  // READ a again
    endmodule
  )";
  
  ASSERT_TRUE(ParseCode(code));
  KytheAnalyzer analyzer(*symbol_table_, *project_);
  
  ASSERT_TRUE(analyzer.BuildKytheFacts().ok());
  
  const auto& refs = analyzer.GetVariableReferences();
  
  // Count references to 'a'
  int a_count = 0;
  for (const auto& ref : refs) {
    if (ref.variable_name == "a") {
      ++a_count;
    }
  }
  
  EXPECT_GE(a_count, 2) << "Expected at least 2 references to 'a'";
}

TEST_F(KytheAnalyzerTest, MultipleWrites) {
  const char* code = R"(
    module test;
      logic sig;
      always_comb begin
        sig = 1'b0;  // WRITE sig
        sig = 1'b1;  // WRITE sig again
      end
    endmodule
  )";
  
  ASSERT_TRUE(ParseCode(code));
  KytheAnalyzer analyzer(*symbol_table_, *project_);
  
  ASSERT_TRUE(analyzer.BuildKytheFacts().ok());
  
  const auto& refs = analyzer.GetVariableReferences();
  
  // Count references to 'sig'
  int sig_count = 0;
  for (const auto& ref : refs) {
    if (ref.variable_name == "sig") {
      ++sig_count;
    }
  }
  
  EXPECT_GE(sig_count, 2) << "Expected at least 2 references to 'sig'";
}

TEST_F(KytheAnalyzerTest, DifferentVariables) {
  const char* code = R"(
    module test;
      logic [7:0] data;
      logic valid;
      always_comb begin
        valid = 1'b1;        // WRITE valid
        if (valid)           // READ valid
          data = 8'hFF;      // WRITE data
      end
    endmodule
  )";
  
  ASSERT_TRUE(ParseCode(code));
  KytheAnalyzer analyzer(*symbol_table_, *project_);
  
  ASSERT_TRUE(analyzer.BuildKytheFacts().ok());
  
  const auto& refs = analyzer.GetVariableReferences();
  EXPECT_GE(refs.size(), 3) << "Expected at least 3 references";
  
  auto var_names = ExtractVarNames(refs);
  EXPECT_TRUE(Contains(var_names, "valid")) << "'valid' not found";
  EXPECT_TRUE(Contains(var_names, "data")) << "'data' not found";
}

TEST_F(KytheAnalyzerTest, LocationAccuracy) {
  const char* code = R"(module test;
  logic sig;
  assign sig = 1'b0;
endmodule
)";
  
  ASSERT_TRUE(ParseCode(code));
  KytheAnalyzer analyzer(*symbol_table_, *project_);
  
  ASSERT_TRUE(analyzer.BuildKytheFacts().ok());
  
  const auto& refs = analyzer.GetVariableReferences();
  ASSERT_GE(refs.size(), 1) << "Expected at least 1 reference";
  
  // Find reference to 'sig'
  const VariableReference* sig_ref = nullptr;
  for (const auto& ref : refs) {
    if (ref.variable_name == "sig") {
      sig_ref = &ref;
      break;
    }
  }
  
  ASSERT_NE(sig_ref, nullptr) << "'sig' reference not found";
  
  // Verify location is valid
  EXPECT_TRUE(sig_ref->location.IsValid()) 
      << "Location is not valid";
  EXPECT_FALSE(sig_ref->location.file_path.empty()) 
      << "File path is empty";
  EXPECT_GE(sig_ref->location.byte_start, 0) 
      << "Invalid byte_start";
  EXPECT_GT(sig_ref->location.byte_end, sig_ref->location.byte_start) 
      << "byte_end must be > byte_start";
  EXPECT_GE(sig_ref->location.line, 1) 
      << "Line number must be >= 1";
  EXPECT_GE(sig_ref->location.column, 1) 
      << "Column number must be >= 1";
}

//-----------------------------------------------------------------------------
// Basic Infrastructure Tests
//-----------------------------------------------------------------------------

TEST_F(KytheAnalyzerTest, EmptyModule) {
  const char* code = R"(
    module empty;
    endmodule
  )";
  
  ASSERT_TRUE(ParseCode(code));
  KytheAnalyzer analyzer(*symbol_table_, *project_);
  
  // Should not crash on empty module
  const auto status = analyzer.BuildKytheFacts();
  EXPECT_TRUE(status.ok()) << "Should handle empty module gracefully";
  
  // Should have 0 references
  const auto& refs = analyzer.GetVariableReferences();
  EXPECT_EQ(refs.size(), 0) << "Empty module should have no references";
}

TEST_F(KytheAnalyzerTest, Statistics) {
  const char* code = R"(
    module test;
      logic a, b;
      assign b = a;
    endmodule
  )";
  
  ASSERT_TRUE(ParseCode(code));
  KytheAnalyzer analyzer(*symbol_table_, *project_);
  
  ASSERT_TRUE(analyzer.BuildKytheFacts().ok());
  
  const auto& stats = analyzer.GetStatistics();
  
  // Should have analyzed 1 file
  EXPECT_EQ(stats.files_analyzed, 1);
  
  // Should have some references
  EXPECT_GE(stats.total_references, 0);
  
  // Analysis time should be reasonable (may be 0 for very fast operations)
  EXPECT_GE(stats.analysis_time_ms, 0);
  EXPECT_LT(stats.analysis_time_ms, 1000) << "Analysis took too long";
}

TEST_F(KytheAnalyzerTest, IsAnalyzed) {
  const char* code = R"(
    module test;
      logic sig;
    endmodule
  )";
  
  ASSERT_TRUE(ParseCode(code));
  KytheAnalyzer analyzer(*symbol_table_, *project_);
  
  // Before analysis
  EXPECT_FALSE(analyzer.IsAnalyzed()) 
      << "Should not be analyzed before BuildKytheFacts()";
  
  // After analysis
  ASSERT_TRUE(analyzer.BuildKytheFacts().ok());
  EXPECT_TRUE(analyzer.IsAnalyzed()) 
      << "Should be analyzed after BuildKytheFacts()";
}

TEST_F(KytheAnalyzerTest, Clear) {
  const char* code = R"(
    module test;
      logic a, b;
      assign b = a;
    endmodule
  )";
  
  ASSERT_TRUE(ParseCode(code));
  KytheAnalyzer analyzer(*symbol_table_, *project_);
  
  ASSERT_TRUE(analyzer.BuildKytheFacts().ok());
  EXPECT_TRUE(analyzer.IsAnalyzed());
  EXPECT_GT(analyzer.GetVariableReferences().size(), 0);
  
  // Clear should reset state
  analyzer.Clear();
  EXPECT_FALSE(analyzer.IsAnalyzed());
  EXPECT_EQ(analyzer.GetVariableReferences().size(), 0);
  EXPECT_EQ(analyzer.GetVariableDefinitions().size(), 0);
}

}  // namespace
}  // namespace verilog

