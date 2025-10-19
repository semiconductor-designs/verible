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

// Include File Resolver for SystemVerilog Preprocessing
// 
// This class resolves `include directives by searching through a list of
// include directories, handling relative paths, and caching results.
//
// Example usage:
//   IncludeFileResolver resolver({"/path/to/includes", "/other/path"});
//   auto content = resolver.ResolveInclude("dv_macros.svh");

#ifndef VERIBLE_VERILOG_ANALYSIS_INCLUDE_FILE_RESOLVER_H_
#define VERIBLE_VERILOG_ANALYSIS_INCLUDE_FILE_RESOLVER_H_

#include <filesystem>
#include <map>
#include <memory>
#include <string>
#include <string_view>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/status/status.h"
#include "verible/common/strings/mem-block.h"
#include "verible/common/text/macro-definition.h"

namespace verilog {

// Forward declarations
class VerilogPreprocess;

// For accessing preprocessor data
struct VerilogPreprocessData;

// Resolves `include directives for SystemVerilog preprocessing
class IncludeFileResolver {
 public:
  // Construct with a list of search paths for include files
  explicit IncludeFileResolver(
      const std::vector<std::string>& search_paths);

  // Resolve an include file and return its contents
  // 
  // Search order:
  // 1. Relative to current_file (if provided)
  // 2. Search through include paths in order
  // 
  // Args:
  //   include_filename: The filename from `include "filename"
  //   current_file: Path of the file containing the `include directive
  // 
  // Returns:
  //   Content of the included file, or error if not found
  absl::StatusOr<std::string_view> ResolveInclude(
      std::string_view include_filename,
      std::string_view current_file = "");

  // Check if an include would create a circular dependency
  // Must be called before ResolveInclude to track the include chain
  absl::Status PushInclude(std::string_view filename);
  
  // Pop the include stack after processing
  void PopInclude();

  // Get the current include depth (for debugging)
  size_t GetIncludeDepth() const { return include_stack_.size(); }

  // Clear all cached files (for testing)
  void ClearCache() { file_cache_.clear(); }

  // =========================================================================
  // Feature 2: Pre-Include Support (v5.4.0)
  // =========================================================================

  // Preload include files and extract their macro definitions
  // 
  // This processes the specified include files through the preprocessor and
  // extracts all macro definitions, making them available for subsequent parsing.
  // 
  // Args:
  //   pre_include_files: List of filenames to process before the main file
  // 
  // Returns:
  //   OK status if all files were processed successfully,
  //   error otherwise (file not found, circular includes, etc.)
  absl::Status PreloadIncludes(
      const std::vector<std::string>& pre_include_files);

  // Get the preprocessor data (including macros) from pre-included files
  // 
  // Returns:
  //   Pointer to VerilogPreprocessData, or nullptr if no pre-includes loaded
  const VerilogPreprocessData* GetPreloadedData() const {
    return preloaded_data_.get();
  }

 private:
  // Try to find file in the filesystem
  absl::StatusOr<std::filesystem::path> FindIncludeFile(
      std::string_view include_filename,
      std::string_view current_file) const;

  // Load file contents into cache
  absl::StatusOr<std::string_view> LoadFile(
      const std::filesystem::path& filepath);

  // Search paths for include files
  std::vector<std::filesystem::path> search_paths_;

  // Cache of loaded files (path -> content)
  std::map<std::string, std::shared_ptr<verible::MemBlock>> file_cache_;

  // Stack of currently processing includes (for cycle detection)
  std::vector<std::string> include_stack_;

  // Preprocessor data from pre-included files (v5.4.0)
  std::unique_ptr<VerilogPreprocessData> preloaded_data_;
};

}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_INCLUDE_FILE_RESOLVER_H_

