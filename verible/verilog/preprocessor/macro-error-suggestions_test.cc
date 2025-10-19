// Copyright 2017-2020 The Verible Authors.
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

#include "verible/verilog/preprocessor/macro-error-suggestions.h"

#include <string>
#include <vector>

#include "gtest/gtest.h"

namespace verilog {
namespace {

// Test 1: UVM macro detection
TEST(MacroErrorSuggestionsTest, DetectsUVMMacros) {
  EXPECT_TRUE(IsKnownUVMMacro("uvm_object_utils"));
  EXPECT_TRUE(IsKnownUVMMacro("uvm_component_utils"));
  EXPECT_TRUE(IsKnownUVMMacro("uvm_field_int"));
  EXPECT_TRUE(IsKnownUVMMacro("uvm_info"));
  EXPECT_TRUE(IsKnownUVMMacro("uvm_object_new"));
  EXPECT_TRUE(IsKnownUVMMacro("uvm_do_with"));
  
  // Starts with uvm_ pattern
  EXPECT_TRUE(IsKnownUVMMacro("uvm_custom_macro"));
}

// Test 2: OpenTitan macro detection
TEST(MacroErrorSuggestionsTest, DetectsOpenTitanMacros) {
  EXPECT_TRUE(IsKnownOpenTitanMacro("DV_CHECK"));
  EXPECT_TRUE(IsKnownOpenTitanMacro("DV_CHECK_FATAL"));
  EXPECT_TRUE(IsKnownOpenTitanMacro("DV_COMMON_CLK_CONSTRAINT"));
  EXPECT_TRUE(IsKnownOpenTitanMacro("DV_MUBI8_DIST"));
  EXPECT_TRUE(IsKnownOpenTitanMacro("gmv"));
  
  // Starts with DV_ pattern
  EXPECT_TRUE(IsKnownOpenTitanMacro("DV_CUSTOM_CHECK"));
}

// Test 3: Package file suggestion from file path
TEST(MacroErrorSuggestionsTest, SuggestsPackageFile) {
  // Test with _env suffix
  EXPECT_EQ(SuggestPackageFile("hw/ip/aes/dv/env/aes_env.sv"),
            "hw/ip/aes/dv/env/aes_pkg.sv");
  
  // Test with _agent suffix
  EXPECT_EQ(SuggestPackageFile("hw/ip/uart/dv/env/uart_agent.sv"),
            "hw/ip/uart/dv/env/uart_pkg.sv");
  
  // Test with _config suffix
  EXPECT_EQ(SuggestPackageFile("path/to/my_config.sv"),
            "path/to/my_pkg.sv");
  
  // Test without suffix
  EXPECT_EQ(SuggestPackageFile("path/to/module.sv"),
            "path/to/module_pkg.sv");
  
  // Test without directory
  EXPECT_EQ(SuggestPackageFile("test_env.sv"),
            "test_pkg.sv");
}

// Test 4: Include path suggestions for known macros
TEST(MacroErrorSuggestionsTest, SuggestsIncludePathsForUVM) {
  std::vector<std::string> empty_paths;
  std::string error = GetMacroErrorWithSuggestions(
      "uvm_object_utils", "my_class.sv", empty_paths);
  
  // Should mention UVM
  EXPECT_NE(error.find("UVM macro"), std::string::npos);
  
  // Should suggest include path
  EXPECT_NE(error.find("third_party/uvm/src"), std::string::npos);
  
  // Should suggest package file
  EXPECT_NE(error.find("my_pkg.sv"), std::string::npos);
}

// Test 5: Multi-line error formatting
TEST(MacroErrorSuggestionsTest, FormatsMultiLineError) {
  std::vector<std::string> paths = {"include1", "include2"};
  std::string error = GetMacroErrorWithSuggestions(
      "UNKNOWN_MACRO", "test.sv", paths);
  
  // Should have error header
  EXPECT_NE(error.find("Error expanding macro"), std::string::npos);
  EXPECT_NE(error.find("UNKNOWN_MACRO"), std::string::npos);
  
  // Should list solutions
  EXPECT_NE(error.find("solutions"), std::string::npos) 
      << "Error message should contain 'solutions'";
  
  // Should list current include paths
  EXPECT_NE(error.find("include1"), std::string::npos);
  EXPECT_NE(error.find("include2"), std::string::npos);
}

// Test 6: Non-UVM macro (should not suggest UVM paths)
TEST(MacroErrorSuggestionsTest, DoesNotSuggestUVMForNonUVMMacros) {
  std::vector<std::string> empty_paths;
  std::string error = GetMacroErrorWithSuggestions(
      "CUSTOM_MACRO", "my_file.sv", empty_paths);
  
  // Should NOT mention UVM specifically
  EXPECT_EQ(error.find("UVM macro"), std::string::npos);
  
  // Should have generic suggestions
  EXPECT_NE(error.find("solutions"), std::string::npos);
  EXPECT_NE(error.find("--include_paths"), std::string::npos);
}

}  // namespace
}  // namespace verilog

