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

// Tests for multiline string literals with triple quotes (SV-2023 Feature 2)
// IEEE 1800-2023: Python-style triple-quoted strings for readable multiline literals

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Basic multiline string
TEST(MultilineStringTest, BasicMultiline) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m;\n"
    "  string s = \"\"\"Line 1\n"
    "Line 2\n"
    "Line 3\"\"\";\n"
    "endmodule\n", 5011);
}

// Test 2: In $display
TEST(MultilineStringTest, InDisplay) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m;\n"
    "  initial $display(\"\"\"Status: OK\n"
    "Value: %d\"\"\", x);\n"
    "endmodule\n", 5012);
}

// Test 3: With indentation
TEST(MultilineStringTest, WithIndentation) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m;\n"
    "  string doc = \"\"\"\n"
    "    Parameter: width\n"
    "    Default: 8\n"
    "    Range: 1-32\n"
    "  \"\"\";\n"
    "endmodule\n", 5013);
}

// Test 4: Empty multiline string
TEST(MultilineStringTest, EmptyString) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m; string s = \"\"\"\"\"\"; endmodule\n", 5014);
}

// Test 5: Single-line triple-quoted
TEST(MultilineStringTest, SingleLineTripleQuoted) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m; string s = \"\"\"Hello World\"\"\"; endmodule\n", 5015);
}

}  // namespace
}  // namespace verilog

