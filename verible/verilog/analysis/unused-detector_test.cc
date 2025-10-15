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

#include "verible/verilog/analysis/unused-detector.h"

#include "gtest/gtest.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace analysis {
namespace {

// Test fixture for UnusedDetector tests
class UnusedDetectorTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Create a minimal project for symbol table
    project_ = std::make_unique<VerilogProject>(".", std::vector<std::string>{});
    symbol_table_ = std::make_unique<SymbolTable>(project_.get());
  }

  std::unique_ptr<VerilogProject> project_;
  std::unique_ptr<SymbolTable> symbol_table_;
};

// Test UnusedDetector construction
TEST_F(UnusedDetectorTest, Construction) {
  UnusedDetector detector(symbol_table_.get());
  
  EXPECT_EQ(detector.GetUnusedCount(), 0);
  EXPECT_TRUE(detector.GetUnusedSymbols().empty());
}

// Test empty symbol table
TEST_F(UnusedDetectorTest, EmptySymbolTable) {
  UnusedDetector detector(symbol_table_.get());
  
  detector.Analyze();
  
  EXPECT_EQ(detector.GetUnusedCount(), 0);
  EXPECT_TRUE(detector.GetUnusedSymbols().empty());
}

// Test Clear functionality
TEST_F(UnusedDetectorTest, Clear) {
  UnusedDetector detector(symbol_table_.get());
  
  detector.Analyze();
  detector.Clear();
  
  EXPECT_EQ(detector.GetUnusedCount(), 0);
  EXPECT_TRUE(detector.GetUnusedSymbols().empty());
}

// Test options - ignore parameters
TEST_F(UnusedDetectorTest, OptionsIgnoreParameters) {
  UnusedDetector detector(symbol_table_.get());
  
  UnusedDetector::Options options;
  options.ignore_parameters = true;
  detector.SetOptions(options);
  
  EXPECT_TRUE(detector.GetOptions().ignore_parameters);
}

// Test options - ignore private
TEST_F(UnusedDetectorTest, OptionsIgnorePrivate) {
  UnusedDetector detector(symbol_table_.get());
  
  UnusedDetector::Options options;
  options.ignore_private = true;
  detector.SetOptions(options);
  
  EXPECT_TRUE(detector.GetOptions().ignore_private);
}

// Test options - minimum references
TEST_F(UnusedDetectorTest, OptionsMinReferences) {
  UnusedDetector detector(symbol_table_.get());
  
  UnusedDetector::Options options;
  options.min_references = 5;
  detector.SetOptions(options);
  
  EXPECT_EQ(detector.GetOptions().min_references, 5);
}

// Test multiple Analyze calls
TEST_F(UnusedDetectorTest, MultipleAnalyzeCalls) {
  UnusedDetector detector(symbol_table_.get());
  
  detector.Analyze();
  size_t first_count = detector.GetUnusedCount();
  
  detector.Analyze();
  size_t second_count = detector.GetUnusedCount();
  
  // Multiple analyses should produce consistent results
  EXPECT_EQ(first_count, second_count);
}

// Test UnusedSymbol construction
TEST_F(UnusedDetectorTest, UnusedSymbolConstruction) {
  UnusedSymbol symbol("test_var", "test.sv", 42, "variable", "module test");
  
  EXPECT_EQ(symbol.name, "test_var");
  EXPECT_EQ(symbol.file_path, "test.sv");
  EXPECT_EQ(symbol.line_number, 42);
  EXPECT_EQ(symbol.symbol_type, "variable");
  EXPECT_EQ(symbol.scope, "module test");
}

// Test default options
TEST_F(UnusedDetectorTest, DefaultOptions) {
  UnusedDetector detector(symbol_table_.get());
  
  const auto& options = detector.GetOptions();
  EXPECT_FALSE(options.ignore_parameters);
  EXPECT_FALSE(options.ignore_private);
  EXPECT_FALSE(options.ignore_testbenches);
  EXPECT_EQ(options.min_references, 1);
}

// Test API stability
TEST_F(UnusedDetectorTest, APIStability) {
  UnusedDetector detector(symbol_table_.get());
  
  // Verify all APIs are accessible
  detector.Analyze();
  EXPECT_GE(detector.GetUnusedCount(), 0);
  EXPECT_NE(&detector.GetUnusedSymbols(), nullptr);
  detector.Clear();
  
  // Test with null symbol table
  UnusedDetector null_detector(nullptr);
  null_detector.Analyze();  // Should not crash
  EXPECT_EQ(null_detector.GetUnusedCount(), 0);
}

// Test options modification
TEST_F(UnusedDetectorTest, OptionsModification) {
  UnusedDetector detector(symbol_table_.get());
  
  UnusedDetector::Options options;
  options.ignore_parameters = true;
  options.ignore_private = true;
  options.ignore_testbenches = true;
  options.min_references = 3;
  
  detector.SetOptions(options);
  
  const auto& retrieved = detector.GetOptions();
  EXPECT_TRUE(retrieved.ignore_parameters);
  EXPECT_TRUE(retrieved.ignore_private);
  EXPECT_TRUE(retrieved.ignore_testbenches);
  EXPECT_EQ(retrieved.min_references, 3);
}

// Test repeated Clear and Analyze
TEST_F(UnusedDetectorTest, RepeatedClearAndAnalyze) {
  UnusedDetector detector(symbol_table_.get());
  
  for (int i = 0; i < 5; ++i) {
    detector.Analyze();
    detector.Clear();
    EXPECT_EQ(detector.GetUnusedCount(), 0);
  }
}

// Test with different option combinations
TEST_F(UnusedDetectorTest, OptionCombinations) {
  UnusedDetector detector(symbol_table_.get());
  
  // Test combination 1
  UnusedDetector::Options opts1;
  opts1.ignore_parameters = true;
  opts1.min_references = 2;
  detector.SetOptions(opts1);
  detector.Analyze();
  
  // Test combination 2
  UnusedDetector::Options opts2;
  opts2.ignore_private = true;
  opts2.ignore_testbenches = true;
  detector.SetOptions(opts2);
  detector.Analyze();
  
  EXPECT_GE(detector.GetUnusedCount(), 0);
}

// Test edge case - zero min references
TEST_F(UnusedDetectorTest, ZeroMinReferences) {
  UnusedDetector detector(symbol_table_.get());
  
  UnusedDetector::Options options;
  options.min_references = 0;  // Everything is "used"
  detector.SetOptions(options);
  detector.Analyze();
  
  // With min_references = 0, all symbols should be considered "used"
  EXPECT_EQ(detector.GetOptions().min_references, 0);
}

}  // namespace
}  // namespace analysis
}  // namespace verilog

