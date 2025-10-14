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

// Tests for type parameter restrictions (SV-2023 Feature 5)
// IEEE 1800-2023: Restrict type parameters to specific categories

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: type enum restriction
TEST(TypeRestrictionsTest, EnumRestriction) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "class C #(type enum T);\n"
    "  T data;\n"
    "endclass\n", 5041);
}

// Test 2: type struct restriction
TEST(TypeRestrictionsTest, StructRestriction) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m #(type struct entry_t);\n"
    "  entry_t buffer[$];\n"
    "endmodule\n", 5042);
}

// Test 3: type class restriction
TEST(TypeRestrictionsTest, ClassRestriction) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "class Registry #(type class handler_t);\n"
    "  handler_t obj;\n"
    "endclass\n", 5043);
}

// Test 4: Multiple type restrictions
TEST(TypeRestrictionsTest, MultipleRestrictions) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "class C #(type enum E, type struct S, type class T);\n"
    "  E state; S data; T handler;\n"
    "endclass\n", 5044);
}

// Test 5: With defaults
TEST(TypeRestrictionsTest, WithDefaults) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m #(type enum state_t = int);\n"
    "  state_t state;\n"
    "endmodule\n", 5045);
}

}  // namespace
}  // namespace verilog

