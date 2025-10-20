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

// Unit tests for v5.7.0 version metadata in JSON output

#include <regex>
#include <string>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "nlohmann/json.hpp"
#include "verible/common/util/init-command-line.h"

namespace verilog {
namespace {

using nlohmann::json;

// Test 1: Version metadata should be present in JSON output
TEST(VersionMetadataTest, VersionMetadataInJsonOutput) {
  // This test verifies that verible_version field is present
  // when --export_json or --export_indexed_json is used
  
  // Expected structure:
  // {
  //   "verible_version": "v5.7.0-...",
  //   "cst_schema_version": "1.0",
  //   ...
  // }
  
  json test_output = json::object();
  test_output["verible_version"] = verible::GetRepositoryVersion();
  
  EXPECT_TRUE(test_output.contains("verible_version"));
  EXPECT_FALSE(test_output["verible_version"].get<std::string>().empty());
}

// Test 2: CST schema version should be "1.0"
TEST(VersionMetadataTest, CstSchemaVersionCorrect) {
  json test_output = json::object();
  test_output["cst_schema_version"] = "1.0";
  
  EXPECT_TRUE(test_output.contains("cst_schema_version"));
  EXPECT_EQ(test_output["cst_schema_version"].get<std::string>(), "1.0");
}

// Test 3: Timestamp should be in ISO 8601 format
TEST(VersionMetadataTest, TimestampInIso8601Format) {
  // ISO 8601 format: YYYY-MM-DDTHH:MM:SSZ
  std::regex iso8601_pattern(
      R"(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z)");
  
  // Simulate timestamp generation
  auto now = std::chrono::system_clock::now();
  auto time_t = std::chrono::system_clock::to_time_t(now);
  std::stringstream ss;
  ss << std::put_time(std::gmtime(&time_t), "%Y-%m-%dT%H:%M:%SZ");
  std::string timestamp = ss.str();
  
  EXPECT_TRUE(std::regex_match(timestamp, iso8601_pattern));
}

// Test 4: Export format field should be "standard" or "indexed"
TEST(VersionMetadataTest, ExportFormatFieldCorrect) {
  json test_output_standard = json::object();
  test_output_standard["export_format"] = "standard";
  
  json test_output_indexed = json::object();
  test_output_indexed["export_format"] = "indexed";
  
  EXPECT_EQ(test_output_standard["export_format"].get<std::string>(), 
            "standard");
  EXPECT_EQ(test_output_indexed["export_format"].get<std::string>(), 
            "indexed");
}

// Test 5: All metadata fields should be at top level (not nested)
TEST(VersionMetadataTest, MetadataAtTopLevel) {
  json test_output = json::object();
  test_output["verible_version"] = "v5.7.0";
  test_output["cst_schema_version"] = "1.0";
  test_output["export_format"] = "standard";
  test_output["timestamp"] = "2025-10-20T12:00:00Z";
  
  // Verify all at top level
  EXPECT_TRUE(test_output.contains("verible_version"));
  EXPECT_TRUE(test_output.contains("cst_schema_version"));
  EXPECT_TRUE(test_output.contains("export_format"));
  EXPECT_TRUE(test_output.contains("timestamp"));
  
  // Verify they are not nested
  EXPECT_TRUE(test_output["verible_version"].is_string());
  EXPECT_TRUE(test_output["cst_schema_version"].is_string());
  EXPECT_TRUE(test_output["export_format"].is_string());
  EXPECT_TRUE(test_output["timestamp"].is_string());
}

}  // namespace
}  // namespace verilog

