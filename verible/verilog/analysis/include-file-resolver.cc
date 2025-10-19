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

#include <algorithm>
#include <filesystem>
#include <memory>
#include <string>
#include <string_view>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "verible/common/strings/mem-block.h"
#include "verible/common/util/file-util.h"

namespace verilog {

IncludeFileResolver::IncludeFileResolver(
    const std::vector<std::string>& search_paths) {
  // Convert search paths to filesystem::path for easier manipulation
  search_paths_.reserve(search_paths.size());
  for (const auto& path : search_paths) {
    search_paths_.push_back(std::filesystem::path(path));
  }
}

absl::StatusOr<std::string_view> IncludeFileResolver::ResolveInclude(
    std::string_view include_filename,
    std::string_view current_file) {
  // Try to find the file in the filesystem
  auto filepath_or = FindIncludeFile(include_filename, current_file);
  if (!filepath_or.ok()) {
    return filepath_or.status();
  }

  // Load and cache the file
  return LoadFile(*filepath_or);
}

absl::Status IncludeFileResolver::PushInclude(std::string_view filename) {
  // Check for circular includes
  std::string filename_str(filename);
  auto it = std::find(include_stack_.begin(), include_stack_.end(), 
                      filename_str);
  if (it != include_stack_.end()) {
    // Build error message showing the cycle
    std::string cycle_path = absl::StrCat("Circular include detected: ");
    for (const auto& f : include_stack_) {
      absl::StrAppend(&cycle_path, f, " -> ");
    }
    absl::StrAppend(&cycle_path, filename);
    return absl::FailedPreconditionError(cycle_path);
  }

  include_stack_.push_back(filename_str);
  return absl::OkStatus();
}

void IncludeFileResolver::PopInclude() {
  if (!include_stack_.empty()) {
    include_stack_.pop_back();
  }
}

absl::StatusOr<std::filesystem::path> IncludeFileResolver::FindIncludeFile(
    std::string_view include_filename,
    std::string_view current_file) const {
  std::filesystem::path include_path(include_filename);

  // Strategy 1: If include is an absolute path, use it directly
  if (include_path.is_absolute()) {
    if (std::filesystem::exists(include_path)) {
      return include_path;
    }
    return absl::NotFoundError(
        absl::StrCat("Include file not found: ", include_filename));
  }

  // Strategy 2: Try relative to current file's directory
  if (!current_file.empty()) {
    std::filesystem::path current_path(current_file);
    auto relative_path = current_path.parent_path() / include_path;
    if (std::filesystem::exists(relative_path)) {
      return std::filesystem::canonical(relative_path);
    }
  }

  // Strategy 3: Search through include paths
  for (const auto& search_path : search_paths_) {
    auto candidate = search_path / include_path;
    if (std::filesystem::exists(candidate)) {
      return std::filesystem::canonical(candidate);
    }
  }

  // Not found anywhere
  return absl::NotFoundError(
      absl::StrCat("Include file not found: ", include_filename,
                   " (searched ", search_paths_.size(), " directories)"));
}

absl::StatusOr<std::string_view> IncludeFileResolver::LoadFile(
    const std::filesystem::path& filepath) {
  // Convert to string for map lookup
  std::string filepath_str = filepath.string();

  // Check if already cached
  auto it = file_cache_.find(filepath_str);
  if (it != file_cache_.end()) {
    return it->second->AsStringView();
  }

  // Load file from disk
  auto content_or = verible::file::GetContentAsMemBlock(filepath_str);
  if (!content_or.ok()) {
    return content_or.status();
  }

  // Store in cache (use shared_ptr for safety)
  auto content = std::shared_ptr<verible::MemBlock>(
      std::move(*content_or));
  auto view = content->AsStringView();
  file_cache_[filepath_str] = content;

  return view;
}

}  // namespace verilog

