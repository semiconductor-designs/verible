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

// Tests for DPI enhancements in SystemVerilog
// IEEE 1800-2017 Section 35: Direct Programming Interface (DPI)
// M14 Week 2: Complete DPI implementation

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Basic DPI import (verify existing)
TEST(DPIEnhancedTest, BasicDPIImport) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  import \"DPI-C\" function int basic_func(input int x);\n"
      "endmodule\n", 14101);
}

// Test 2: DPI with open array []
TEST(DPIEnhancedTest, DPIWithOpenArray) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  import \"DPI-C\" function void process_array(\n"
      "    input int arr[],\n"
      "    input int size\n"
      "  );\n"
      "endmodule\n", 14102);
}

// Test 3: DPI context function
TEST(DPIEnhancedTest, DPIContextFunction) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  import \"DPI-C\" context function void context_func();\n"
      "endmodule\n", 14103);
}

// Test 4: DPI context task export
TEST(DPIEnhancedTest, DPIContextTaskExport) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  export \"DPI-C\" context task context_task;\n"
      "  task context_task();\n"
      "    $display(\"task\");\n"
      "  endtask\n"
      "endmodule\n", 14104);
}

// Test 5: DPI pure function
TEST(DPIEnhancedTest, DPIPureFunction) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  import \"DPI-C\" pure function int pure_calc(input int x);\n"
      "endmodule\n", 14105);
}

// Test 6: DPI with chandle type
TEST(DPIEnhancedTest, DPIWithChandle) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  import \"DPI-C\" function void handle_chandle(\n"
      "    input chandle ptr\n"
      "  );\n"
      "endmodule\n", 14106);
}

// Test 7: DPI with string type
TEST(DPIEnhancedTest, DPIWithString) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  import \"DPI-C\" function void handle_string(\n"
      "    input string str\n"
      "  );\n"
      "endmodule\n", 14107);
}

// Test 8: DPI function returning string
TEST(DPIEnhancedTest, DPIReturningString) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
      "module m;\n"
      "  import \"DPI-C\" function string get_name();\n"
      "endmodule\n", 14108);
}

}  // namespace
}  // namespace verilog

