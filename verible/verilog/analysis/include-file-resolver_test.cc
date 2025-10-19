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

}  // namespace
}  // namespace verilog

