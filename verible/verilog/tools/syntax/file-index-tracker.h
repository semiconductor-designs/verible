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

// FileIndexTracker: Tracks file indices for multi-file batch processing
// Used with --export_indexed_json flag to map <indexed> placeholders to paths

#ifndef VERIBLE_VERILOG_TOOLS_SYNTAX_FILE_INDEX_TRACKER_H_
#define VERIBLE_VERILOG_TOOLS_SYNTAX_FILE_INDEX_TRACKER_H_

#include <map>
#include <string>
#include <string_view>

#include "nlohmann/json.hpp"

namespace verilog {

// Tracks file indices for multi-file batch processing
// Maps filenames to string indices ("0", "1", "2", ...)
// Normalizes paths to absolute for consistency
class FileIndexTracker {
 public:
  FileIndexTracker() = default;
  
  // Add a file and get its index ID
  // Returns the index ID as a string ("0", "1", etc.)
  // If file already exists, returns existing index
  // Converts relative paths to absolute paths
  std::string AddFile(std::string_view filename);
  
  // Get index ID for a file (returns empty string if not found)
  std::string GetIndexId(std::string_view filename) const;
  
  // Export file index as JSON: {"0": "/abs/path/file1.sv", "1": "/abs/path/file2.sv"}
  nlohmann::json ExportAsJson() const;
  
  // Get total number of files tracked
  size_t GetFileCount() const { return file_to_index_.size(); }
  
  // Clear all tracked files
  void Clear() {
    file_to_index_.clear();
    next_index_ = 0;
  }
  
 private:
  std::map<std::string, std::string> file_to_index_;  // absolute_path -> "0", "1", ...
  size_t next_index_ = 0;
};

}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_SYNTAX_FILE_INDEX_TRACKER_H_

