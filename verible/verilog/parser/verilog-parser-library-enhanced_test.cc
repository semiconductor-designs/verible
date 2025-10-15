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

// Tests for library and config enhancements in SystemVerilog
// IEEE 1364-2001 Section 13: Configuring the contents of a design
// M13 Sprint 2: Library Enhancement

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Basic library declaration (verify existing)
TEST(LibraryEnhancedTest, BasicLibraryDeclaration) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "library work file1.v file2.v;\n", 13101);
}

// Test 2: Library with -incdir
TEST(LibraryEnhancedTest, LibraryWithIncdir) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "library work file.v -incdir ./inc;\n", 13102);
}

// Test 3: Config with liblist clause (multiple libraries)
TEST(LibraryEnhancedTest, ConfigWithLiblistMultiple) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "config cfg;\n"
      "  design top;\n"
      "  default liblist lib1 lib2 lib3;\n"
      "endconfig\n", 13103);
}

// Test 4: Config instance with liblist
TEST(LibraryEnhancedTest, ConfigInstanceWithLiblist) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 liblist mylib;\n"
      "endconfig\n", 13104);
}

// Test 5: Config instance with use
TEST(LibraryEnhancedTest, ConfigInstanceWithUse) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "config cfg;\n"
      "  design top;\n"
      "  instance top.u1 use mylib.cell1;\n"
      "endconfig\n", 13105);
}

// Test 6: Config cell with liblist
TEST(LibraryEnhancedTest, ConfigCellWithLiblist) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "config cfg;\n"
      "  design top;\n"
      "  cell work.mycell liblist lib1 lib2;\n"
      "endconfig\n", 13106);
}

// Test 7: Mixed config rules
TEST(LibraryEnhancedTest, ConfigMixedRules) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "config cfg;\n"
      "  design top;\n"
      "  default liblist lib1;\n"
      "  instance top.u1 liblist lib2;\n"
      "  cell work.mycell use lib3.cell;\n"
      "endconfig\n", 13107);
}

}  // namespace
}  // namespace verilog

