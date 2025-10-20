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

// Unit tests for FileIndexTracker

#include "verible/verilog/tools/syntax/file-index-tracker.h"

#include <filesystem>
#include <fstream>
#include <string>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "nlohmann/json.hpp"

namespace verilog {
namespace {

using nlohmann::json;

// Test 1: Add single file, get index "0"
TEST(FileIndexTrackerTest, AddFileSingleFile) {
  FileIndexTracker tracker;
  
  std::string index = tracker.AddFile("test.sv");
  
  EXPECT_EQ(index, "0");
  EXPECT_EQ(tracker.GetFileCount(), 1);
}

// Test 2: Add multiple files, get sequential indices
TEST(FileIndexTrackerTest, AddFileMultipleFiles) {
  FileIndexTracker tracker;
  
  std::string index0 = tracker.AddFile("file1.sv");
  std::string index1 = tracker.AddFile("file2.sv");
  std::string index2 = tracker.AddFile("file3.sv");
  
  EXPECT_EQ(index0, "0");
  EXPECT_EQ(index1, "1");
  EXPECT_EQ(index2, "2");
  EXPECT_EQ(tracker.GetFileCount(), 3);
}

// Test 3: Adding same file twice returns same index
TEST(FileIndexTrackerTest, AddFileDuplicate) {
  FileIndexTracker tracker;
  
  std::string index1 = tracker.AddFile("test.sv");
  std::string index2 = tracker.AddFile("test.sv");
  
  EXPECT_EQ(index1, index2);
  EXPECT_EQ(index1, "0");
  EXPECT_EQ(tracker.GetFileCount(), 1);  // Still only 1 file
}

// Test 4: Get index for existing file
TEST(FileIndexTrackerTest, GetIndexIdExisting) {
  FileIndexTracker tracker;
  
  tracker.AddFile("test.sv");
  std::string index = tracker.GetIndexId("test.sv");
  
  EXPECT_EQ(index, "0");
}

// Test 5: Get index for non-existent file returns empty string
TEST(FileIndexTrackerTest, GetIndexIdNonExistent) {
  FileIndexTracker tracker;
  
  tracker.AddFile("test.sv");
  std::string index = tracker.GetIndexId("nonexistent.sv");
  
  EXPECT_TRUE(index.empty());
}

// Test 6: Export as JSON has correct format
TEST(FileIndexTrackerTest, ExportAsJsonFormat) {
  FileIndexTracker tracker;
  
  // Create temporary test files to get absolute paths
  std::filesystem::path temp_dir = std::filesystem::temp_directory_path();
  std::filesystem::path file1 = temp_dir / "test_file1.sv";
  std::filesystem::path file2 = temp_dir / "test_file2.sv";
  
  // Create the files
  {
    std::ofstream(file1).close();
    std::ofstream(file2).close();
  }
  
  tracker.AddFile(file1.string());
  tracker.AddFile(file2.string());
  
  json exported = tracker.ExportAsJson();
  
  // Verify structure: {"0": "path1", "1": "path2"}
  EXPECT_TRUE(exported.is_object());
  EXPECT_TRUE(exported.contains("0"));
  EXPECT_TRUE(exported.contains("1"));
  EXPECT_EQ(exported["0"].get<std::string>(), file1.string());
  EXPECT_EQ(exported["1"].get<std::string>(), file2.string());
  
  // Cleanup
  std::filesystem::remove(file1);
  std::filesystem::remove(file2);
}

// Test 7: Relative paths converted to absolute
TEST(FileIndexTrackerTest, AbsolutePathNormalization) {
  FileIndexTracker tracker;
  
  // Add with relative path
  std::string index = tracker.AddFile("test.sv");
  
  json exported = tracker.ExportAsJson();
  std::string stored_path = exported["0"].get<std::string>();
  
  // Stored path should be absolute (contains directory separators)
  // On Unix: starts with '/', on Windows: contains ':'
  #ifdef _WIN32
    EXPECT_TRUE(stored_path.find(':') != std::string::npos);
  #else
    EXPECT_TRUE(stored_path[0] == '/');
  #endif
}

// Test 8: Clear functionality
TEST(FileIndexTrackerTest, ClearFunctionality) {
  FileIndexTracker tracker;
  
  tracker.AddFile("file1.sv");
  tracker.AddFile("file2.sv");
  EXPECT_EQ(tracker.GetFileCount(), 2);
  
  tracker.Clear();
  EXPECT_EQ(tracker.GetFileCount(), 0);
  
  // After clear, adding new file starts from index "0" again
  std::string index = tracker.AddFile("file3.sv");
  EXPECT_EQ(index, "0");
}

// Test 9: Empty tracker exports empty JSON object
TEST(FileIndexTrackerTest, EmptyTrackerExport) {
  FileIndexTracker tracker;
  
  json exported = tracker.ExportAsJson();
  
  EXPECT_TRUE(exported.is_object());
  EXPECT_TRUE(exported.empty());
}

}  // namespace
}  // namespace verilog

