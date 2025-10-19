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

// Unit tests for UVM Macro Registry
// Phase 2.2: Tests updated to match new API

#include "verible/verilog/preprocessor/uvm-macros.h"

#include "gtest/gtest.h"

namespace verilog {
namespace preprocessor {
namespace {

// Test that registry is non-empty
TEST(UVMMacroRegistry, RegistryNotEmpty) {
  const auto& registry = GetUvmMacroRegistry();
  EXPECT_FALSE(registry.empty());
  EXPECT_GT(registry.size(), 10);  // Should have at least 10 macros
}

// Test specific macro presence
TEST(UVMMacroRegistry, HasCommonMacros) {
  const auto& registry = GetUvmMacroRegistry();
  
  // Object utils macros
  EXPECT_NE(registry.find("uvm_object_utils"), registry.end());
  EXPECT_NE(registry.find("uvm_object_utils_begin"), registry.end());
  EXPECT_NE(registry.find("uvm_object_utils_end"), registry.end());
  
  // Component utils macros
  EXPECT_NE(registry.find("uvm_component_utils"), registry.end());
  
  // Field automation macros
  EXPECT_NE(registry.find("uvm_field_int"), registry.end());
  EXPECT_NE(registry.find("uvm_field_object"), registry.end());
  
  // Reporting macros
  EXPECT_NE(registry.find("uvm_info"), registry.end());
  EXPECT_NE(registry.find("uvm_warning"), registry.end());
  EXPECT_NE(registry.find("uvm_error"), registry.end());
  EXPECT_NE(registry.find("uvm_fatal"), registry.end());
}

// Test macro not in registry
TEST(UVMMacroRegistry, MacroNotFound) {
  const auto& registry = GetUvmMacroRegistry();
  EXPECT_EQ(registry.find("unknown_macro"), registry.end());
  EXPECT_EQ(registry.find("not_a_uvm_macro"), registry.end());
}

// Test complex macro list
TEST(UVMMacroRegistry, ComplexMacrosList) {
  const auto& complex_macros = GetComplexUvmMacroNames();
  EXPECT_FALSE(complex_macros.empty());
  EXPECT_GE(complex_macros.size(), 3);  // At least a few complex macros
}

// Test that a specific macro has correct structure
TEST(UVMMacroRegistry, MacroHasCorrectStructure) {
  const auto& registry = GetUvmMacroRegistry();
  auto it = registry.find("uvm_object_utils");
  ASSERT_NE(it, registry.end());
  
  const auto& macro = it->second;
  EXPECT_EQ(macro.Name(), "uvm_object_utils");
  EXPECT_TRUE(macro.IsCallable());  // Has parameters
}

// Test that field int macro is callable
TEST(UVMMacroRegistry, FieldIntMacroIsCallable) {
  const auto& registry = GetUvmMacroRegistry();
  auto it = registry.find("uvm_field_int");
  ASSERT_NE(it, registry.end());
  
  const auto& macro = it->second;
  EXPECT_TRUE(macro.IsCallable());
  EXPECT_GE(macro.Parameters().size(), 1);  // Should have at least ARG parameter
}

}  // namespace
}  // namespace preprocessor
}  // namespace verilog
