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

// UVM Integration Parser Tests - Phase 8
// Tests complete UVM components with all features combined

#include <string>

#include "gtest/gtest.h"
#include "absl/status/status.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

namespace verilog {
namespace {

// Test 1: Complete UVM sequence item (from test fixtures)
TEST(UVMIntegrationTest, CompleteSequenceItem) {
  const char* kTestCode = R"(
class simple_item extends uvm_sequence_item;
  rand bit data;
  
  `uvm_object_utils_begin(simple_item)
    `uvm_field_int(data, UVM_DEFAULT)
  `uvm_object_utils_end
  
  function new(string name = "simple_item");
    super.new(name);
  endfunction
endclass
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until full UVM support implemented
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 2: UVM sequence item with constraints (alert_esc_seq_item pattern)
TEST(UVMIntegrationTest, SequenceItemWithConstraints) {
  const char* kTestCode = R"(
class alert_esc_seq_item extends uvm_sequence_item;
  rand bit s_alert_send;
  rand int unsigned ping_delay;
  rand int unsigned ack_delay;
  
  `uvm_object_utils_begin(alert_esc_seq_item)
    `uvm_field_int(s_alert_send, UVM_DEFAULT)
    `uvm_field_int(ping_delay, UVM_DEFAULT)
    `uvm_field_int(ack_delay, UVM_DEFAULT)
  `uvm_object_utils_end
  
  extern constraint delay_c;
  
  function new(string name = "alert_esc_seq_item");
    super.new(name);
  endfunction
endclass

constraint alert_esc_seq_item::delay_c {
  soft ping_delay dist {0 :/ 5, [1:10] :/ 5};
  soft ack_delay dist {0 :/ 5, [1:10] :/ 5};
}
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until full UVM support implemented
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 3: Parameterized UVM base class (cip_base_vseq pattern)
TEST(UVMIntegrationTest, ParameterizedBaseClass) {
  const char* kTestCode = R"(
class dv_base_reg_block;
endclass

class cip_base_env_cfg;
endclass

class cip_base_vseq #(
  type RAL_T = dv_base_reg_block,
  type CFG_T = cip_base_env_cfg
) extends uvm_sequence;
  RAL_T ral;
  CFG_T cfg;
  
  `uvm_object_param_utils_begin(cip_base_vseq#(RAL_T, CFG_T))
  `uvm_object_utils_end
  
  function new(string name = "cip_base_vseq");
    super.new(name);
  endfunction
  
  virtual task body();
    `uvm_info(`gfn, "Starting sequence", UVM_LOW)
  endtask
endclass
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until full UVM support implemented
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 4: UVM agent with component utils
TEST(UVMIntegrationTest, UVMAgent) {
  const char* kTestCode = R"(
class uart_agent extends uvm_agent;
  uart_driver driver;
  uart_monitor monitor;
  uart_sequencer sequencer;
  
  `uvm_component_utils(uart_agent)
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    driver = uart_driver::type_id::create("driver", this);
    monitor = uart_monitor::type_id::create("monitor", this);
    sequencer = uart_sequencer::type_id::create("sequencer", this);
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
  endfunction
endclass
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until full UVM support implemented
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 5: UVM sequence with uvm_do macros
TEST(UVMIntegrationTest, SequenceWithDoMacros) {
  const char* kTestCode = R"(
class test_sequence extends uvm_sequence#(test_item);
  `uvm_object_utils(test_sequence)
  
  function new(string name = "test_sequence");
    super.new(name);
  endfunction
  
  virtual task body();
    `uvm_do(req)
    `uvm_do_with(req, {addr == 0; data inside {[1:10]};})
    repeat (5) begin
      `uvm_do(req)
    end
  endtask
endclass
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until full UVM support implemented
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 6: Complex constraints with all operators
TEST(UVMIntegrationTest, ComplexConstraints) {
  const char* kTestCode = R"(
class complex_item extends uvm_sequence_item;
  rand int mode;
  rand int delay;
  rand int timeout;
  rand bit enable;
  rand int arr[4];
  
  `uvm_object_utils(complex_item)
  
  constraint mode_c {
    mode inside {0, 1, 2};
    mode dist {0 := 30, 1 := 50, 2 := 20};
  }
  
  extern constraint delay_c;
  
  constraint order_c {
    solve mode before delay;
    solve delay before timeout;
  }
  
  constraint array_c {
    foreach (arr[i]) {
      arr[i] dist {[0:10] :/ 100};
    }
  }
endclass

constraint complex_item::delay_c {
  soft delay dist {0 := 10, [1:10] := 40, [11:100] :/ 50};
  enable -> (delay < timeout);
  mode == 0 <-> (delay inside {[1:5]});
}
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until full UVM support implemented
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 7: Nested parameterized classes
TEST(UVMIntegrationTest, NestedParameterization) {
  const char* kTestCode = R"(
class base #(type T1 = int, type T2 = bit);
  T1 data1;
  T2 data2;
  `uvm_object_param_utils_begin(base#(T1, T2))
  `uvm_object_utils_end
endclass

class derived #(
  type CFG_T = int,
  parameter int WIDTH = 8
) extends base#(CFG_T, logic[WIDTH-1:0]);
  CFG_T config;
  `uvm_object_param_utils_begin(derived#(CFG_T, WIDTH))
  `uvm_object_utils_end
endclass
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until full UVM support implemented
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

// Test 8: UVM component with nested macro patterns
TEST(UVMIntegrationTest, ComponentWithNestedMacros) {
  const char* kTestCode = R"(
class test_env extends uvm_env;
  `uvm_component_utils(test_env)
  
  test_agent agent;
  test_scoreboard sb;
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    `uvm_info(`gfn, "Building environment", UVM_LOW)
    
    agent = test_agent::type_id::create("agent", this);
    sb = test_scoreboard::type_id::create("sb", this);
  endfunction
endclass
)";
  
  VerilogAnalyzer analyzer(kTestCode, "test.sv");
  // TDD Red: This will FAIL until full UVM support implemented
  EXPECT_TRUE(analyzer.Analyze().ok());
  const auto& syntax_tree = analyzer.SyntaxTree();
  EXPECT_NE(syntax_tree, nullptr);
}

}  // namespace
}  // namespace verilog

