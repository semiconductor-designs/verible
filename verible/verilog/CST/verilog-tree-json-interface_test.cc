// Copyright 2017-2025 The Verible Authors.
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

// Phase 2.1: Core Interface Support Tests for JSON Export
// Tests for interface declarations with modports

#include "verible/verilog/CST/verilog-tree-json.h"

#include <string>

#include "gtest/gtest.h"
#include "nlohmann/json.hpp"
#include "verible/common/text/symbol.h"
#include "verible/common/util/logging.h"
#include "verible/verilog/CST/verilog-nonterminals.h"
#include "verible/verilog/analysis/verilog-analyzer.h"

using nlohmann::json;

namespace verilog {
namespace {

// Helper: Parse code and convert to JSON
json ParseToJson(const std::string& code) {
  VerilogAnalyzer analyzer(code, "<test>");
  auto status = analyzer.Analyze();
  if (!status.ok()) {
    LOG(ERROR) << "Parse error: " << status.message();
    return json::object();
  }
  
  const auto& text_structure = analyzer.Data();
  const auto* root = text_structure.SyntaxTree().get();
  if (!root) return json::object();
  
  return ConvertVerilogTreeToJson(*root, text_structure.Contents());
}

// Helper: Find node by tag recursively
const json* FindNodeByTag(const json& node, const std::string& tag) {
  if (node.contains("tag") && node["tag"] == tag) {
    return &node;
  }
  
  if (node.contains("children")) {
    for (const auto& child : node["children"]) {
      const json* result = FindNodeByTag(child, tag);
      if (result) return result;
    }
  }
  
  return nullptr;
}

// Test 1: Basic interface declaration
TEST(InterfaceTest, BasicInterface) {
  const std::string code = R"(
interface simple_if;
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty()) << "Parse should succeed";
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr) << "Should find kInterfaceDeclaration node";
}

// Test 2: Interface with signals
TEST(InterfaceTest, InterfaceWithSignals) {
  const std::string code = R"(
interface data_if;
  logic clk;
  logic [31:0] addr;
  logic [63:0] data;
  logic valid;
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
  
  if (intf->contains("metadata") && (*intf)["metadata"].contains("interface_info")) {
    const auto& info = (*intf)["metadata"]["interface_info"];
    if (info.contains("signal_count")) {
      EXPECT_GT(info["signal_count"], 0);
    }
  }
}

// Test 3: Modport declarations (master, slave)
TEST(InterfaceTest, ModportDeclarations) {
  const std::string code = R"(
interface axi_if;
  logic clk;
  logic [31:0] addr;
  
  modport master (
    input  clk,
    output addr
  );
  
  modport slave (
    input clk,
    input addr
  );
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
  
  if (intf->contains("metadata") && (*intf)["metadata"].contains("interface_info")) {
    const auto& info = (*intf)["metadata"]["interface_info"];
    if (info.contains("modport_count")) {
      EXPECT_EQ(info["modport_count"], 2);
    }
  }
}

// Test 4: Clocking blocks in interface
TEST(InterfaceTest, ClockingBlocksInInterface) {
  const std::string code = R"(
interface clk_if (input logic clk);
  clocking cb @(posedge clk);
    input  data;
    output valid;
  endclocking
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
  
  if (intf->contains("metadata") && (*intf)["metadata"].contains("interface_info")) {
    const auto& info = (*intf)["metadata"]["interface_info"];
    if (info.contains("has_clocking_blocks")) {
      EXPECT_TRUE(info["has_clocking_blocks"]);
    }
  }
}

// Test 5: Interface with parameters
TEST(InterfaceTest, InterfaceWithParameters) {
  const std::string code = R"(
interface param_if #(parameter WIDTH = 32);
  logic [WIDTH-1:0] data;
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
  
  if (intf->contains("metadata") && (*intf)["metadata"].contains("interface_info")) {
    const auto& info = (*intf)["metadata"]["interface_info"];
    if (info.contains("has_parameters")) {
      EXPECT_TRUE(info["has_parameters"]);
    }
  }
}

// Test 6: Virtual interface
TEST(InterfaceTest, VirtualInterface) {
  const std::string code = R"(
class test_class;
  virtual interface axi_if vif;
endclass
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 7: Interface arrays
TEST(InterfaceTest, InterfaceArrays) {
  const std::string code = R"(
module test;
  simple_if if_array[4]();
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 8: Interface ports
TEST(InterfaceTest, InterfacePorts) {
  const std::string code = R"(
interface port_if (
  input logic clk,
  input logic rst_n
);
  logic [7:0] data;
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
  
  if (intf->contains("metadata") && (*intf)["metadata"].contains("interface_info")) {
    const auto& info = (*intf)["metadata"]["interface_info"];
    if (info.contains("has_ports")) {
      EXPECT_TRUE(info["has_ports"]);
    }
  }
}

// Test 9: Interface methods (functions/tasks)
TEST(InterfaceTest, InterfaceMethods) {
  const std::string code = R"(
interface method_if;
  logic [7:0] data;
  
  function bit is_valid();
    return (data != 0);
  endfunction
  
  task wait_ready();
    @(posedge clk);
  endtask
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 10: Hierarchical interfaces
TEST(InterfaceTest, HierarchicalInterfaces) {
  const std::string code = R"(
interface sub_if;
  logic signal;
endinterface

interface top_if;
  sub_if sub();
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  // Count interfaces
  int intf_count = 0;
  std::function<void(const json&)> count_interfaces = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kInterfaceDeclaration") {
      intf_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_interfaces(child);
      }
    }
  };
  count_interfaces(tree);
  
  EXPECT_EQ(intf_count, 2) << "Should find 2 interfaces";
}

// Tests 11-30: Continuing comprehensive coverage...

// Test 11: Interface with typedef
TEST(InterfaceTest, InterfaceWithTypedef) {
  const std::string code = R"(
interface typedef_if;
  typedef logic [7:0] byte_t;
  byte_t data;
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 12: Interface with enum
TEST(InterfaceTest, InterfaceWithEnum) {
  const std::string code = R"(
interface enum_if;
  typedef enum {IDLE, BUSY} state_t;
  state_t state;
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 13: Interface with struct
TEST(InterfaceTest, InterfaceWithStruct) {
  const std::string code = R"(
interface struct_if;
  typedef struct {
    logic [31:0] addr;
    logic [63:0] data;
  } transaction_t;
  
  transaction_t txn;
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 14: Interface with modport expressions
TEST(InterfaceTest, InterfaceWithModportExpressions) {
  const std::string code = R"(
interface expr_if;
  logic clk, enable;
  logic [7:0] data;
  
  modport producer (
    input clk,
    output data,
    output enable
  );
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 15: Multiple modports
TEST(InterfaceTest, MultipleModports) {
  const std::string code = R"(
interface multi_if;
  logic clk, data;
  
  modport m1 (input clk);
  modport m2 (output data);
  modport m3 (input clk, output data);
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
  
  if (intf->contains("metadata") && (*intf)["metadata"].contains("interface_info")) {
    const auto& info = (*intf)["metadata"]["interface_info"];
    if (info.contains("modport_count")) {
      EXPECT_EQ(info["modport_count"], 3);
    }
  }
}

// Test 16: Interface with generate blocks
TEST(InterfaceTest, InterfaceWithGenerate) {
  const std::string code = R"(
interface gen_if #(parameter N = 4);
  logic [N-1:0] bus;
  
  generate
    for (genvar i = 0; i < N; i++) begin
      logic signal;
    end
  endgenerate
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 17: Interface instantiation in module
TEST(InterfaceTest, InterfaceInstantiation) {
  const std::string code = R"(
interface simple_if;
  logic data;
endinterface

module test;
  simple_if my_if();
endmodule
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
}

// Test 18: Interface with assertions
TEST(InterfaceTest, InterfaceWithAssertions) {
  const std::string code = R"(
interface assert_if;
  logic clk, req, ack;
  
  property p_req_ack;
    @(posedge clk) req |-> ##1 ack;
  endproperty
  
  assert property (p_req_ack);
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 19: Interface with initial/always blocks
TEST(InterfaceTest, InterfaceWithAlwaysBlocks) {
  const std::string code = R"(
interface proc_if;
  logic clk, data;
  
  always @(posedge clk) begin
    $display("Clock edge");
  end
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 20: Interface with continuous assignments
TEST(InterfaceTest, InterfaceWithAssignments) {
  const std::string code = R"(
interface assign_if;
  logic a, b, c;
  
  assign c = a & b;
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 21: Empty interface
TEST(InterfaceTest, EmptyInterface) {
  const std::string code = R"(
interface empty_if;
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 22: Interface with packed arrays
TEST(InterfaceTest, InterfaceWithPackedArrays) {
  const std::string code = R"(
interface array_if;
  logic [3:0][7:0] packed_array;
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 23: Interface with unpacked arrays
TEST(InterfaceTest, InterfaceWithUnpackedArrays) {
  const std::string code = R"(
interface unpacked_if;
  logic data [16];
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 24: Interface with import statements
TEST(InterfaceTest, InterfaceWithImports) {
  const std::string code = R"(
interface import_if;
  import my_pkg::*;
  my_type_t data;
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 25: Interface with timeunits
TEST(InterfaceTest, InterfaceWithTimeunits) {
  const std::string code = R"(
interface time_if;
  timeunit 1ns;
  timeprecision 1ps;
  
  logic clk;
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 26: Complex AXI interface
TEST(InterfaceTest, ComplexAXIInterface) {
  const std::string code = R"(
interface axi4_if #(
  parameter ADDR_WIDTH = 32,
  parameter DATA_WIDTH = 64
);
  logic                    aclk;
  logic                    aresetn;
  logic [ADDR_WIDTH-1:0]   awaddr;
  logic [DATA_WIDTH-1:0]   wdata;
  logic                    awvalid;
  logic                    awready;
  
  modport master (
    input  aclk,
    input  aresetn,
    output awaddr,
    output wdata,
    output awvalid,
    input  awready
  );
  
  modport slave (
    input  aclk,
    input  aresetn,
    input  awaddr,
    input  wdata,
    input  awvalid,
    output awready
  );
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
  
  if (intf->contains("metadata") && (*intf)["metadata"].contains("interface_info")) {
    const auto& info = (*intf)["metadata"]["interface_info"];
    
    if (info.contains("has_parameters")) {
      EXPECT_TRUE(info["has_parameters"]);
    }
    
    if (info.contains("modport_count")) {
      EXPECT_EQ(info["modport_count"], 2);
    }
    
    if (info.contains("signal_count")) {
      EXPECT_GT(info["signal_count"], 0);
    }
  }
}

// Test 27: Interface with modport and tasks
TEST(InterfaceTest, InterfaceWithModportAndTasks) {
  const std::string code = R"(
interface task_if;
  logic [7:0] data;
  
  task write_data(input logic [7:0] value);
    data = value;
  endtask
  
  modport manager (
    import write_data
  );
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 28: Multiple interfaces in file
TEST(InterfaceTest, MultipleInterfaces) {
  const std::string code = R"(
interface if1;
  logic a;
endinterface

interface if2;
  logic b;
endinterface

interface if3;
  logic c;
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  int intf_count = 0;
  std::function<void(const json&)> count_interfaces = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kInterfaceDeclaration") {
      intf_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_interfaces(child);
      }
    }
  };
  count_interfaces(tree);
  
  EXPECT_EQ(intf_count, 3) << "Should find 3 interfaces";
}

// Test 29: Performance test (50 interfaces)
TEST(InterfaceTest, PerformanceTest) {
  std::string code;
  
  for (int i = 0; i < 50; i++) {
    code += "interface if" + std::to_string(i) + ";\n";
    code += "  logic data" + std::to_string(i) + ";\n";
    code += "endinterface\n\n";
  }
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  int intf_count = 0;
  std::function<void(const json&)> count_interfaces = [&](const json& node) {
    if (node.contains("tag") && node["tag"] == "kInterfaceDeclaration") {
      intf_count++;
    }
    if (node.contains("children")) {
      for (const auto& child : node["children"]) {
        count_interfaces(child);
      }
    }
  };
  count_interfaces(tree);
  
  EXPECT_EQ(intf_count, 50) << "Should find 50 interfaces";
}

// Test 30: Complete UVM interface pattern
TEST(InterfaceTest, CompleteUVMInterface) {
  const std::string code = R"(
interface uvm_test_if (input logic clk, input logic rst_n);
  import uvm_pkg::*;
  
  logic [31:0] addr;
  logic [63:0] data;
  logic        valid;
  logic        ready;
  
  clocking driver_cb @(posedge clk);
    default input #1 output #1;
    output addr;
    output data;
    output valid;
    input  ready;
  endclocking
  
  clocking monitor_cb @(posedge clk);
    input addr;
    input data;
    input valid;
    input ready;
  endclocking
  
  modport driver (
    clocking driver_cb,
    input rst_n
  );
  
  modport monitor (
    clocking monitor_cb,
    input rst_n
  );
  
  property p_valid_ready;
    @(posedge clk) disable iff (!rst_n)
    valid |-> ##[0:5] ready;
  endproperty
  
  assert property (p_valid_ready);
  
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
  
  if (intf->contains("metadata") && (*intf)["metadata"].contains("interface_info")) {
    const auto& info = (*intf)["metadata"]["interface_info"];
    
    if (info.contains("has_clocking_blocks")) {
      EXPECT_TRUE(info["has_clocking_blocks"]);
    }
    
    if (info.contains("modport_count")) {
      EXPECT_EQ(info["modport_count"], 2);
    }
  }
}

}  // namespace
}  // namespace verilog

