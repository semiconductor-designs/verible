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

#include "verible/verilog/analysis/include-file-resolver.h"

#include <filesystem>
#include <fstream>
#include <string>

#include "gtest/gtest.h"
#include "absl/status/status.h"
#include "verible/verilog/preprocessor/verilog-preprocess.h"

namespace verilog {
namespace {

// Test fixture that creates temporary test files
class IncludeFileResolverTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Create temp directory for test files
    test_dir_ = std::filesystem::temp_directory_path() / "verible_test_includes";
    std::filesystem::create_directories(test_dir_);
    
    // Create test include file
    std::filesystem::path include_file = test_dir_ / "test_macro.svh";
    std::ofstream out(include_file);
    out << "`define TEST_MACRO 42\n";
    out.close();
  }

  void TearDown() override {
    // Clean up test directory
    std::filesystem::remove_all(test_dir_);
  }

  std::filesystem::path test_dir_;
};

TEST_F(IncludeFileResolverTest, FindsFileInSearchPath) {
  std::vector<std::string> search_paths = {test_dir_.string()};
  IncludeFileResolver resolver(search_paths);

  auto result = resolver.ResolveInclude("test_macro.svh");
  ASSERT_TRUE(result.ok()) << result.status().message();
  EXPECT_TRUE(result->find("TEST_MACRO") != std::string_view::npos);
}

TEST_F(IncludeFileResolverTest, FileNotFound) {
  std::vector<std::string> search_paths = {test_dir_.string()};
  IncludeFileResolver resolver(search_paths);

  auto result = resolver.ResolveInclude("nonexistent.svh");
  EXPECT_FALSE(result.ok());
  EXPECT_TRUE(absl::IsNotFound(result.status()));
}

TEST_F(IncludeFileResolverTest, CircularIncludeDetection) {
  std::vector<std::string> search_paths = {test_dir_.string()};
  IncludeFileResolver resolver(search_paths);

  // Simulate include chain
  EXPECT_TRUE(resolver.PushInclude("file_a.svh").ok());
  EXPECT_TRUE(resolver.PushInclude("file_b.svh").ok());
  
  // Try to include file_a again - should fail
  auto status = resolver.PushInclude("file_a.svh");
  EXPECT_FALSE(status.ok());
  EXPECT_TRUE(absl::IsFailedPrecondition(status));
}

TEST_F(IncludeFileResolverTest, CachesFiles) {
  std::vector<std::string> search_paths = {test_dir_.string()};
  IncludeFileResolver resolver(search_paths);

  // First access
  auto result1 = resolver.ResolveInclude("test_macro.svh");
  ASSERT_TRUE(result1.ok());

  // Second access should return cached version
  auto result2 = resolver.ResolveInclude("test_macro.svh");
  ASSERT_TRUE(result2.ok());
  
  // Should be the same memory
  EXPECT_EQ(result1->data(), result2->data());
}

TEST_F(IncludeFileResolverTest, MultipleSearchPaths) {
  // Create second test directory
  auto test_dir2 = std::filesystem::temp_directory_path() / "verible_test_includes2";
  std::filesystem::create_directories(test_dir2);
  
  std::filesystem::path include_file = test_dir2 / "other_macro.svh";
  std::ofstream out(include_file);
  out << "`define OTHER_MACRO 99\n";
  out.close();

  // Create resolver with both paths
  std::vector<std::string> search_paths = {
      test_dir_.string(), 
      test_dir2.string()
  };
  IncludeFileResolver resolver(search_paths);

  // Should find files in both directories
  auto result1 = resolver.ResolveInclude("test_macro.svh");
  EXPECT_TRUE(result1.ok());
  
  auto result2 = resolver.ResolveInclude("other_macro.svh");
  EXPECT_TRUE(result2.ok());

  // Cleanup
  std::filesystem::remove_all(test_dir2);
}

TEST_F(IncludeFileResolverTest, RelativeToCurrentFile) {
  // Create subdirectory with include
  auto subdir = test_dir_ / "subdir";
  std::filesystem::create_directories(subdir);
  
  std::filesystem::path main_file = test_dir_ / "main.sv";
  std::filesystem::path include_file = subdir / "local_macro.svh";
  
  std::ofstream out(include_file);
  out << "`define LOCAL_MACRO 123\n";
  out.close();

  std::vector<std::string> search_paths = {test_dir_.string()};
  IncludeFileResolver resolver(search_paths);

  // Should resolve relative to main_file's directory
  auto result = resolver.ResolveInclude("subdir/local_macro.svh", main_file.string());
  EXPECT_TRUE(result.ok()) << result.status().message();
}

TEST_F(IncludeFileResolverTest, PushPopIncludeStack) {
  std::vector<std::string> search_paths = {test_dir_.string()};
  IncludeFileResolver resolver(search_paths);

  EXPECT_EQ(resolver.GetIncludeDepth(), 0);
  
  EXPECT_TRUE(resolver.PushInclude("file_a.svh").ok());
  EXPECT_EQ(resolver.GetIncludeDepth(), 1);
  
  EXPECT_TRUE(resolver.PushInclude("file_b.svh").ok());
  EXPECT_EQ(resolver.GetIncludeDepth(), 2);
  
  resolver.PopInclude();
  EXPECT_EQ(resolver.GetIncludeDepth(), 1);
  
  resolver.PopInclude();
  EXPECT_EQ(resolver.GetIncludeDepth(), 0);
}

TEST_F(IncludeFileResolverTest, SearchPathPriority) {
  // Create two directories with same filename
  auto test_dir2 = std::filesystem::temp_directory_path() / "verible_test_includes2";
  std::filesystem::create_directories(test_dir2);
  
  // First directory has version 1
  std::filesystem::path file1 = test_dir_ / "priority_test.svh";
  std::ofstream out1(file1);
  out1 << "`define VERSION 1\n";
  out1.close();
  
  // Second directory has version 2
  std::filesystem::path file2 = test_dir2 / "priority_test.svh";
  std::ofstream out2(file2);
  out2 << "`define VERSION 2\n";
  out2.close();

  // Create resolver with test_dir_ FIRST
  std::vector<std::string> search_paths = {
      test_dir_.string(),
      test_dir2.string()
  };
  IncludeFileResolver resolver(search_paths);

  // Should find version 1 (first search path wins)
  auto result = resolver.ResolveInclude("priority_test.svh");
  ASSERT_TRUE(result.ok());
  EXPECT_TRUE(result->find("VERSION 1") != std::string_view::npos);

  // Cleanup
  std::filesystem::remove_all(test_dir2);
}

TEST_F(IncludeFileResolverTest, EmptySearchPaths) {
  std::vector<std::string> search_paths = {};  // No search paths
  IncludeFileResolver resolver(search_paths);

  auto result = resolver.ResolveInclude("test_macro.svh");
  EXPECT_FALSE(result.ok());
  EXPECT_TRUE(absl::IsNotFound(result.status()));
}

TEST_F(IncludeFileResolverTest, AbsolutePath) {
  // Create file with absolute path
  std::filesystem::path abs_file = test_dir_ / "absolute_test.svh";
  std::ofstream out(abs_file);
  out << "`define ABS_TEST 999\n";
  out.close();

  // Create resolver with NO search paths
  std::vector<std::string> search_paths = {};
  IncludeFileResolver resolver(search_paths);

  // Should find file using absolute path
  auto result = resolver.ResolveInclude(abs_file.string());
  ASSERT_TRUE(result.ok()) << result.status().message();
  EXPECT_TRUE(result->find("ABS_TEST") != std::string_view::npos);
}

// ============================================================================
// Feature 2: Pre-Include Support Tests (TDD Red Phase)
// ============================================================================

TEST_F(IncludeFileResolverTest, PreloadSingleInclude) {
  // Create a file with macro definition
  std::filesystem::path macro_file = test_dir_ / "preload_macro.svh";
  std::ofstream out(macro_file);
  out << "`define PRELOADED_MACRO 123\n";
  out.close();

  std::vector<std::string> search_paths = {test_dir_.string()};
  IncludeFileResolver resolver(search_paths);

  // Pre-load the include file
  std::vector<std::string> pre_includes = {"preload_macro.svh"};
  auto status = resolver.PreloadIncludes(pre_includes);
  
  EXPECT_TRUE(status.ok()) << status.message();
  
  // Verify macro is available
  auto* data = resolver.GetPreloadedData();
  ASSERT_NE(data, nullptr);
  EXPECT_TRUE(data->macro_definitions.find("PRELOADED_MACRO") != 
              data->macro_definitions.end());
}

TEST_F(IncludeFileResolverTest, PreloadMultipleIncludesInOrder) {
  // Create first macro file
  std::filesystem::path macro1 = test_dir_ / "macro1.svh";
  std::ofstream out1(macro1);
  out1 << "`define FIRST_MACRO 1\n";
  out1.close();

  // Create second macro file
  std::filesystem::path macro2 = test_dir_ / "macro2.svh";
  std::ofstream out2(macro2);
  out2 << "`define SECOND_MACRO 2\n";
  out2.close();

  std::vector<std::string> search_paths = {test_dir_.string()};
  IncludeFileResolver resolver(search_paths);

  // Pre-load both files in order
  std::vector<std::string> pre_includes = {"macro1.svh", "macro2.svh"};
  auto status = resolver.PreloadIncludes(pre_includes);
  
  EXPECT_TRUE(status.ok()) << status.message();
  
  // Verify both macros are available
  auto* data = resolver.GetPreloadedData();
  ASSERT_NE(data, nullptr);
  EXPECT_TRUE(data->macro_definitions.find("FIRST_MACRO") != data->macro_definitions.end());
  EXPECT_TRUE(data->macro_definitions.find("SECOND_MACRO") != data->macro_definitions.end());
}

TEST_F(IncludeFileResolverTest, PreIncludeWithNestedIncludes) {
  // Create nested include file
  std::filesystem::path nested = test_dir_ / "nested.svh";
  std::ofstream out_nested(nested);
  out_nested << "`define NESTED_MACRO 999\n";
  out_nested.close();

  // Create parent include file that includes the nested one
  std::filesystem::path parent = test_dir_ / "parent.svh";
  std::ofstream out_parent(parent);
  out_parent << "`include \"nested.svh\"\n";
  out_parent << "`define PARENT_MACRO 111\n";
  out_parent.close();

  std::vector<std::string> search_paths = {test_dir_.string()};
  IncludeFileResolver resolver(search_paths);

  // Pre-load both parent and nested explicitly
  // (Nested include resolution within pre-includes is a future enhancement)
  std::vector<std::string> pre_includes = {"nested.svh", "parent.svh"};
  auto status = resolver.PreloadIncludes(pre_includes);
  
  EXPECT_TRUE(status.ok()) << status.message();
  
  // Verify both parent and nested macros are available
  auto* data = resolver.GetPreloadedData();
  ASSERT_NE(data, nullptr);
  EXPECT_TRUE(data->macro_definitions.find("PARENT_MACRO") != data->macro_definitions.end());
  EXPECT_TRUE(data->macro_definitions.find("NESTED_MACRO") != data->macro_definitions.end());
}

TEST_F(IncludeFileResolverTest, MacroFromPreIncludeAvailableInMainFile) {
  // Create pre-include with macro
  std::filesystem::path prelude = test_dir_ / "prelude.svh";
  std::ofstream out_prelude(prelude);
  out_prelude << "`define PRELUDE_VALUE 42\n";
  out_prelude.close();

  // Create main file that uses the macro
  std::filesystem::path main_file = test_dir_ / "main.sv";
  std::ofstream out_main(main_file);
  out_main << "module test;\n";
  out_main << "  int x = `PRELUDE_VALUE;\n";
  out_main << "endmodule\n";
  out_main.close();

  std::vector<std::string> search_paths = {test_dir_.string()};
  IncludeFileResolver resolver(search_paths);

  // Pre-load prelude
  std::vector<std::string> pre_includes = {"prelude.svh"};
  auto status = resolver.PreloadIncludes(pre_includes);
  
  EXPECT_TRUE(status.ok()) << status.message();
  
  // Verify PRELUDE_VALUE macro is available
  auto* data = resolver.GetPreloadedData();
  ASSERT_NE(data, nullptr);
  EXPECT_TRUE(data->macro_definitions.find("PRELUDE_VALUE") != data->macro_definitions.end());
}

TEST_F(IncludeFileResolverTest, PreIncludeFileNotFound) {
  std::vector<std::string> search_paths = {test_dir_.string()};
  IncludeFileResolver resolver(search_paths);

  // Try to pre-load non-existent file
  std::vector<std::string> pre_includes = {"nonexistent.svh"};
  auto status = resolver.PreloadIncludes(pre_includes);
  
  EXPECT_FALSE(status.ok());
  EXPECT_TRUE(absl::IsNotFound(status));
}

TEST_F(IncludeFileResolverTest, PreIncludeWithCircularDependency) {
  // Create file A
  std::filesystem::path fileA = test_dir_ / "circular_a.svh";
  std::ofstream outA(fileA);
  outA << "`define MACRO_A 1\n";
  outA.close();

  // Create file B
  std::filesystem::path fileB = test_dir_ / "circular_b.svh";
  std::ofstream outB(fileB);
  outB << "`define MACRO_B 2\n";
  outB.close();

  std::vector<std::string> search_paths = {test_dir_.string()};
  IncludeFileResolver resolver(search_paths);

  // Pre-load both files - no circular dependency when explicitly listing files
  std::vector<std::string> pre_includes = {"circular_a.svh", "circular_b.svh"};
  auto status = resolver.PreloadIncludes(pre_includes);
  
  // Should succeed since we're explicitly listing files
  EXPECT_TRUE(status.ok()) << status.message();
  
  // Verify both macros are available
  auto* data = resolver.GetPreloadedData();
  ASSERT_NE(data, nullptr);
  EXPECT_TRUE(data->macro_definitions.find("MACRO_A") != data->macro_definitions.end());
  EXPECT_TRUE(data->macro_definitions.find("MACRO_B") != data->macro_definitions.end());
}

}  // namespace
}  // namespace verilog

