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

// Tests for `ref static` keyword in task/function arguments (SV-2023 Feature 1)
// IEEE 1800-2023: ref static for FSM state updates via nonblocking assignments

#include "gtest/gtest.h"
#include "verible/common/parser/parser-test-util.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Basic ref static in task
TEST(RefStaticTest, TaskArgument) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m;\n"
    "  task t(ref static logic [7:0] state);\n"
    "    state <= 8'h00;\n"
    "  endtask\n"
    "endmodule\n", 5001);
}

// Test 2: ref static in function
TEST(RefStaticTest, FunctionArgument) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module m;\n"
    "  function void f(ref static int counter);\n"
    "    counter <= counter + 1;\n"
    "  endfunction\n"
    "endmodule\n", 5002);
}

// Test 3: FSM use case
TEST(RefStaticTest, FSMUpdate) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "module fsm;\n"
    "  typedef enum {IDLE, ACTIVE} state_t;\n"
    "  state_t state;\n"
    "  task update_state(ref static state_t s, input event_t evt);\n"
    "    s <= ACTIVE;\n"
    "  endtask\n"
    "  always_ff @(posedge clk) update_state(state, event);\n"
    "endmodule\n", 5003);
}

// Test 4: Multiple ref static args
TEST(RefStaticTest, MultipleArgs) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "task t(ref static int a, ref static logic b);\n"
    "  a <= 0; b <= 1'b0;\n"
    "endtask\n", 5004);
}

// Test 5: Mixed ref and ref static
TEST(RefStaticTest, MixedRefTypes) {
  verible::TestParserAcceptValid<VerilogAnalyzer>(
    "task t(ref int x, ref static int y, input int z);\n"
    "  x = z; y <= z;\n"
    "endtask\n", 5005);
}

}  // namespace
}  // namespace verilog

