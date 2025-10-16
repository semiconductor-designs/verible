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

#ifndef VERIBLE_VERILOG_TOOLS_VERIPG_BATCH_PROCESSOR_H_
#define VERIBLE_VERILOG_TOOLS_VERIPG_BATCH_PROCESSOR_H_

#include <functional>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "verible/verilog/tools/veripg/veripg-validator.h"

namespace verilog {
namespace tools {

// Batch validation results for multiple files
struct BatchResult {
  struct FileResult {
    std::string file_path;
    std::vector<Violation> violations;
    absl::Status status;  // Success or error for this file
    double processing_time_ms = 0.0;
  };
  
  std::vector<FileResult> file_results;
  double total_time_ms = 0.0;
  
  // Summary statistics
  int total_files = 0;
  int files_with_violations = 0;
  int total_violations = 0;
  int failed_files = 0;
};

// Progress callback for batch processing
using ProgressCallback = std::function<void(int current_file, int total_files,
                                             const std::string& current_path)>;

// Batch processor for validating multiple files
class BatchProcessor {
 public:
  BatchProcessor() = default;
  
  // Process multiple files with optional progress callback
  absl::StatusOr<BatchResult> ProcessFiles(
      const std::vector<std::string>& file_paths,
      VeriPGValidator& validator,
      ProgressCallback progress_cb = nullptr);
  
  // Process files in parallel (future enhancement)
  absl::StatusOr<BatchResult> ProcessFilesParallel(
      const std::vector<std::string>& file_paths,
      VeriPGValidator& validator,
      int num_threads = 4,
      ProgressCallback progress_cb = nullptr);
  
  // Generate summary report
  std::string GenerateSummary(const BatchResult& result) const;
  
 private:
  // Helper to process a single file
  BatchResult::FileResult ProcessSingleFile(
      const std::string& file_path,
      VeriPGValidator& validator);
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_VERIPG_BATCH_PROCESSOR_H_

