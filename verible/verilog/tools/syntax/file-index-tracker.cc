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

#include "verible/verilog/tools/syntax/file-index-tracker.h"

#include <filesystem>
#include <string>
#include <string_view>

namespace verilog {

std::string FileIndexTracker::AddFile(std::string_view filename) {
  // Convert to absolute path for consistency
  std::filesystem::path path(filename);
  std::string absolute;
  
  try {
    absolute = std::filesystem::absolute(path).string();
  } catch (const std::filesystem::filesystem_error&) {
    // If absolute path conversion fails, use the original path
    absolute = std::string(filename);
  }
  
  // Check if already exists
  auto it = file_to_index_.find(absolute);
  if (it != file_to_index_.end()) {
    return it->second;
  }
  
  // Add new entry
  std::string index_id = std::to_string(next_index_++);
  file_to_index_[absolute] = index_id;
  return index_id;
}

std::string FileIndexTracker::GetIndexId(std::string_view filename) const {
  std::filesystem::path path(filename);
  std::string absolute;
  
  try {
    absolute = std::filesystem::absolute(path).string();
  } catch (const std::filesystem::filesystem_error&) {
    absolute = std::string(filename);
  }
  
  auto it = file_to_index_.find(absolute);
  return (it != file_to_index_.end()) ? it->second : "";
}

nlohmann::json FileIndexTracker::ExportAsJson() const {
  nlohmann::json result = nlohmann::json::object();
  for (const auto& [filename, index_id] : file_to_index_) {
    result[index_id] = filename;
  }
  return result;
}

}  // namespace verilog

