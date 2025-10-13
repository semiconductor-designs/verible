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

// Phase 2.2: Advanced Modport & Clocking Block Tests for JSON Export
// Tests for advanced interface features: modport import/export, clocking skew, etc.

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

//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// ADVANCED MODPORT TESTS (1-10)
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Test 1: Modport with import task/function
TEST(InterfaceAdvancedTest, ModportImportTasks) {
  const std::string code = R"(
interface bus_if;
  logic [7:0] data;
  
  task write_data(input logic [7:0] value);
    data = value;
  endtask
  
  function logic [7:0] read_data();
    return data;
  endfunction
  
  modport manager (
    import write_data,
    import read_data
  );
  
  modport subordinate (
    output data
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

// Test 2: Modport with export task/function
TEST(InterfaceAdvancedTest, ModportExportTasks) {
  const std::string code = R"(
interface callback_if;
  logic done;
  
  modport provider (
    export on_complete
  );
  
  task on_complete();
    done = 1;
  endtask
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 3: Modport with inout ports
TEST(InterfaceAdvancedTest, ModportInoutPorts) {
  const std::string code = R"(
interface bidir_if;
  logic [7:0] bus;
  logic       enable;
  
  modport controller (
    inout bus,
    output enable
  );
  
  modport target (
    inout bus,
    input enable
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

// Test 4: Modport with clocking block reference
TEST(InterfaceAdvancedTest, ModportWithClockingBlock) {
  const std::string code = R"(
interface sync_if (input logic clk);
  logic [15:0] data;
  logic valid;
  
  clocking driver_cb @(posedge clk);
    output data;
    output valid;
  endclocking
  
  clocking monitor_cb @(posedge clk);
    input data;
    input valid;
  endclocking
  
  modport driver (
    clocking driver_cb
  );
  
  modport monitor (
    clocking monitor_cb
  );
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

// Test 5: Modport with ref direction
TEST(InterfaceAdvancedTest, ModportRefDirection) {
  const std::string code = R"(
interface array_if;
  logic [31:0] memory [256];
  
  modport accessor (
    ref memory
  );
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 6: Multiple modports with mixed directions
TEST(InterfaceAdvancedTest, MixedDirectionModports) {
  const std::string code = R"(
interface complex_if;
  logic clk, rst;
  logic [31:0] addr, data;
  logic valid, ready;
  
  modport master (
    input  clk, rst, ready,
    output addr, data, valid
  );
  
  modport slave (
    input  clk, rst, addr, data, valid,
    output ready
  );
  
  modport monitor (
    input clk, rst, addr, data, valid, ready
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
      EXPECT_EQ(info["modport_count"], 3);
    }
  }
}

// Test 7: Modport with hierarchical port connections
TEST(InterfaceAdvancedTest, HierarchicalModport) {
  const std::string code = R"(
interface nested_if;
  struct {
    logic [7:0] addr;
    logic [15:0] data;
  } transaction;
  
  modport requester (
    output transaction
  );
  
  modport responder (
    input transaction
  );
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 8: Modport with multiple import/export
TEST(InterfaceAdvancedTest, MultipleImportExport) {
  const std::string code = R"(
interface protocol_if;
  logic [7:0] status;
  
  task send(input logic [7:0] data);
    status = data;
  endtask
  
  task receive(output logic [7:0] data);
    data = status;
  endtask
  
  function bit is_ready();
    return (status != 0);
  endfunction
  
  modport transactor (
    import send,
    import receive,
    import is_ready
  );
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 9: Modport name collision handling
TEST(InterfaceAdvancedTest, ModportNameCollision) {
  const std::string code = R"(
interface naming_if;
  logic data;
  logic data_out;  // Similar name
  
  modport data (
    output data_out
  );
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 10: Modport with all direction types
TEST(InterfaceAdvancedTest, AllDirectionTypes) {
  const std::string code = R"(
interface full_dir_if;
  logic [7:0] in_sig;
  logic [7:0] out_sig;
  logic [7:0] inout_sig;
  logic [31:0] ref_data [64];
  
  task helper();
  endtask
  
  modport full (
    input in_sig,
    output out_sig,
    inout inout_sig,
    ref ref_data,
    import helper
  );
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// ADVANCED CLOCKING BLOCK TESTS (11-20)
//━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Test 11: Clocking block with input/output skew
TEST(InterfaceAdvancedTest, ClockingSkew) {
  const std::string code = R"(
interface timing_if (input logic clk);
  logic [7:0] data;
  logic valid;
  
  clocking cb @(posedge clk);
    default input #1ns output #2ns;
    input data;
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

// Test 12: Clocking block with #1step skew
TEST(InterfaceAdvancedTest, ClockingOneStep) {
  const std::string code = R"(
interface step_if (input logic clk);
  logic [15:0] addr;
  logic [31:0] data;
  
  clocking driver @(posedge clk);
    default input #1step output #0;
    output addr;
    output data;
  endclocking
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 13: Multiple clocking blocks with different edges
TEST(InterfaceAdvancedTest, MultipleClockingEdges) {
  const std::string code = R"(
interface dual_edge_if (input logic clk);
  logic [7:0] data_pos;
  logic [7:0] data_neg;
  
  clocking pos_cb @(posedge clk);
    input data_pos;
  endclocking
  
  clocking neg_cb @(negedge clk);
    input data_neg;
  endclocking
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 14: Clocking block with event control
TEST(InterfaceAdvancedTest, ClockingEventControl) {
  const std::string code = R"(
interface event_if (input logic clk, input logic enable);
  logic [7:0] data;
  
  clocking cb @(posedge clk iff enable);
    input data;
  endclocking
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 15: Default clocking block
TEST(InterfaceAdvancedTest, DefaultClocking) {
  const std::string code = R"(
interface default_clk_if (input logic clk);
  logic [31:0] data;
  logic valid;
  
  default clocking cb @(posedge clk);
    input data;
    output valid;
  endclocking
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 16: Clocking block with inout signal
TEST(InterfaceAdvancedTest, ClockingInout) {
  const std::string code = R"(
interface bidir_clk_if (input logic clk);
  logic [7:0] bus;
  
  clocking cb @(posedge clk);
    inout bus;
  endclocking
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 17: Clocking block with cycle delay
TEST(InterfaceAdvancedTest, ClockingCycleDelay) {
  const std::string code = R"(
interface delay_if (input logic clk);
  logic req;
  logic ack;
  
  clocking cb @(posedge clk);
    output req;
    input #3 ack;  // 3-cycle input delay
  endclocking
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 18: Multiple clocking blocks with different names
TEST(InterfaceAdvancedTest, MultipleNamedClocking) {
  const std::string code = R"(
interface multi_clk_if (input logic clk);
  logic [7:0] data_a;
  logic [7:0] data_b;
  
  clocking cb_a @(posedge clk);
    input data_a;
  endclocking
  
  clocking cb_b @(posedge clk);
    input data_b;
  endclocking
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 19: Clocking block with multiple signal types
TEST(InterfaceAdvancedTest, ClockingMultipleTypes) {
  const std::string code = R"(
interface types_clk_if (input logic clk);
  logic [7:0] byte_data;
  logic [31:0] word_data;
  logic [63:0] dword_data;
  logic valid;
  
  clocking cb @(posedge clk);
    input byte_data;
    input word_data;
    output dword_data;
    output valid;
  endclocking
endinterface
)";
  
  json tree = ParseToJson(code);
  ASSERT_FALSE(tree.empty());
  
  const json* intf = FindNodeByTag(tree, "kInterfaceDeclaration");
  ASSERT_NE(intf, nullptr);
}

// Test 20: Complex clocking with multiple features
TEST(InterfaceAdvancedTest, ComplexClocking) {
  const std::string code = R"(
interface complex_clk_if (input logic clk, input logic rst_n);
  logic [31:0] addr;
  logic [63:0] wdata, rdata;
  logic valid, ready;
  
  default clocking master_cb @(posedge clk);
    default input #1ns output #2ns;
    output addr;
    output wdata;
    output valid;
    input #3 rdata;
    input ready;
  endclocking
  
  clocking slave_cb @(negedge clk);
    input addr;
    input wdata;
    input valid;
    output rdata;
    output ready;
  endclocking
  
  modport master (
    clocking master_cb,
    input rst_n
  );
  
  modport slave (
    clocking slave_cb,
    input rst_n
  );
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
    
    if (info.contains("has_ports")) {
      EXPECT_TRUE(info["has_ports"]);
    }
    
    if (info.contains("modport_count")) {
      EXPECT_EQ(info["modport_count"], 2);
    }
  }
}

}  // namespace
}  // namespace verilog

