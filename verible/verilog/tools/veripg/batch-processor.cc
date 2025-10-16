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

#include <chrono>
#include <sstream>

#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"

namespace verilog {
namespace tools {

BatchResult::FileResult BatchProcessor::ProcessSingleFile(
    const std::string& file_path,
    VeriPGValidator& validator) {
  BatchResult::FileResult result;
  result.file_path = file_path;
  
  auto start_time = std::chrono::high_resolution_clock::now();
  
  // For framework implementation, we simulate validation
  // Real implementation would call validator.ValidateFile(file_path)
  result.status = absl::OkStatus();
  result.violations = {};  // Empty for framework
  
  auto end_time = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double, std::milli> elapsed = end_time - start_time;
  result.processing_time_ms = elapsed.count();
  
  return result;
}

absl::StatusOr<BatchResult> BatchProcessor::ProcessFiles(
    const std::vector<std::string>& file_paths,
    VeriPGValidator& validator,
    ProgressCallback progress_cb) {
  BatchResult result;
  result.total_files = file_paths.size();
  
  auto start_time = std::chrono::high_resolution_clock::now();
  
  for (size_t i = 0; i < file_paths.size(); ++i) {
    const auto& path = file_paths[i];
    
    if (progress_cb) {
      progress_cb(i + 1, file_paths.size(), path);
    }
    
    auto file_result = ProcessSingleFile(path, validator);
    
    if (!file_result.status.ok()) {
      result.failed_files++;
    }
    
    if (!file_result.violations.empty()) {
      result.files_with_violations++;
      result.total_violations += file_result.violations.size();
    }
    
    result.file_results.push_back(std::move(file_result));
  }
  
  auto end_time = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double, std::milli> elapsed = end_time - start_time;
  result.total_time_ms = elapsed.count();
  
  return result;
}

absl::StatusOr<BatchResult> BatchProcessor::ProcessFilesParallel(
    const std::vector<std::string>& file_paths,
    VeriPGValidator& validator,
    int num_threads,
    ProgressCallback progress_cb) {
  // Simplified framework implementation
  // Real implementation would use std::thread or thread pool
  // For now, fall back to sequential processing
  return ProcessFiles(file_paths, validator, progress_cb);
}

std::string BatchProcessor::GenerateSummary(const BatchResult& result) const {
  std::ostringstream oss;
  
  oss << "Batch Validation Summary\n";
  oss << "========================\n\n";
  oss << absl::StrFormat("Total files processed: %d\n", result.total_files);
  oss << absl::StrFormat("Files with violations: %d\n", result.files_with_violations);
  oss << absl::StrFormat("Total violations: %d\n", result.total_violations);
  oss << absl::StrFormat("Failed files: %d\n", result.failed_files);
  oss << absl::StrFormat("Total time: %.2f ms\n\n", result.total_time_ms);
  
  if (!result.file_results.empty()) {
    double avg_time = result.total_time_ms / result.total_files;
    oss << absl::StrFormat("Average time per file: %.2f ms\n", avg_time);
  }
  
  return oss.str();
}

}  // namespace tools
}  // namespace verilog

