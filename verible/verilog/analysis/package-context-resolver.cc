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

// Implementation of PackageContextResolver
// Feature 3 (v5.4.0): Package Context Mode
//
// RED PHASE: Stub implementation - all methods return errors
// This allows tests to compile but fail (TDD Red phase)

#include "verible/verilog/analysis/package-context-resolver.h"

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"

namespace verilog {

absl::StatusOr<PackageContext> PackageContextResolver::ParsePackage(
    std::string_view package_file) {
  // RED PHASE: Not implemented yet
  return absl::UnimplementedError(
      absl::StrCat("ParsePackage not implemented: ", package_file));
}

absl::StatusOr<CombinedPackageContext> PackageContextResolver::ParsePackages(
    const std::vector<std::string>& package_files) {
  // RED PHASE: Not implemented yet
  return absl::UnimplementedError("ParsePackages not implemented");
}

absl::StatusOr<std::string> PackageContextResolver::AutoDetectPackageFile(
    std::string_view test_file) {
  // RED PHASE: Not implemented yet
  return absl::UnimplementedError(
      absl::StrCat("AutoDetectPackageFile not implemented: ", test_file));
}

}  // namespace verilog

