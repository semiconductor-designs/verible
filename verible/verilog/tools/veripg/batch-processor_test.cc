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

#include "verible/verilog/tools/veripg/batch-processor.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace verilog {
namespace tools {
namespace {

// Test: Process empty file list
TEST(BatchProcessorTest, ProcessEmptyList) {
  BatchProcessor processor;
  VeriPGValidator validator(nullptr);
  
  std::vector<std::string> files = {};
  auto result = processor.ProcessFiles(files, validator);
  
  ASSERT_TRUE(result.ok());
  EXPECT_EQ(result->total_files, 0);
  EXPECT_EQ(result->files_with_violations, 0);
  EXPECT_EQ(result->total_violations, 0);
}

// Test: Process single file
TEST(BatchProcessorTest, ProcessSingleFile) {
  BatchProcessor processor;
  VeriPGValidator validator(nullptr);
  
  std::vector<std::string> files = {"test.sv"};
  auto result = processor.ProcessFiles(files, validator);
  
  ASSERT_TRUE(result.ok());
  EXPECT_EQ(result->total_files, 1);
  EXPECT_EQ(result->file_results.size(), 1);
  EXPECT_EQ(result->file_results[0].file_path, "test.sv");
}

// Test: Process multiple files
TEST(BatchProcessorTest, ProcessMultipleFiles) {
  BatchProcessor processor;
  VeriPGValidator validator(nullptr);
  
  std::vector<std::string> files = {"file1.sv", "file2.sv", "file3.sv"};
  auto result = processor.ProcessFiles(files, validator);
  
  ASSERT_TRUE(result.ok());
  EXPECT_EQ(result->total_files, 3);
  EXPECT_EQ(result->file_results.size(), 3);
  EXPECT_GT(result->total_time_ms, 0.0);
}

// Test: Progress callback
TEST(BatchProcessorTest, ProgressCallback) {
  BatchProcessor processor;
  VeriPGValidator validator(nullptr);
  
  std::vector<std::string> files = {"file1.sv", "file2.sv"};
  
  int callback_count = 0;
  auto progress_cb = [&](int current, int total, const std::string& path) {
    callback_count++;
    EXPECT_GT(current, 0);
    EXPECT_EQ(total, 2);
    EXPECT_FALSE(path.empty());
  };
  
  auto result = processor.ProcessFiles(files, validator, progress_cb);
  
  ASSERT_TRUE(result.ok());
  EXPECT_EQ(callback_count, 2);
}

// Test: Generate summary
TEST(BatchProcessorTest, GenerateSummary) {
  BatchProcessor processor;
  
  BatchResult result;
  result.total_files = 5;
  result.files_with_violations = 2;
  result.total_violations = 10;
  result.failed_files = 1;
  result.total_time_ms = 123.45;
  
  std::string summary = processor.GenerateSummary(result);
  
  EXPECT_THAT(summary, testing::HasSubstr("Total files processed: 5"));
  EXPECT_THAT(summary, testing::HasSubstr("Files with violations: 2"));
  EXPECT_THAT(summary, testing::HasSubstr("Total violations: 10"));
  EXPECT_THAT(summary, testing::HasSubstr("Failed files: 1"));
  EXPECT_THAT(summary, testing::HasSubstr("123.45"));
}

// Test: Parallel processing (framework)
TEST(BatchProcessorTest, ProcessFilesParallel) {
  BatchProcessor processor;
  VeriPGValidator validator(nullptr);
  
  std::vector<std::string> files = {"file1.sv", "file2.sv", "file3.sv"};
  auto result = processor.ProcessFilesParallel(files, validator, 2);
  
  ASSERT_TRUE(result.ok());
  EXPECT_EQ(result->total_files, 3);
}

// Test: Performance tracking
TEST(BatchProcessorTest, PerformanceTracking) {
  BatchProcessor processor;
  VeriPGValidator validator(nullptr);
  
  std::vector<std::string> files = {"file1.sv", "file2.sv"};
  auto result = processor.ProcessFiles(files, validator);
  
  ASSERT_TRUE(result.ok());
  EXPECT_GT(result->total_time_ms, 0.0);
  
  for (const auto& file_result : result->file_results) {
    EXPECT_GE(file_result.processing_time_ms, 0.0);
  }
}

}  // namespace
}  // namespace tools
}  // namespace verilog

