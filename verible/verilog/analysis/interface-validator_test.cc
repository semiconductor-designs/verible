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

#include "verible/verilog/analysis/interface-validator.h"

#include <memory>
#include <string_view>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "gtest/gtest.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace analysis {
namespace {

// Helper class for interface validator tests
class InterfaceValidatorTest : public ::testing::Test {
 protected:
  void SetUp() override {
    project_ = std::make_unique<VerilogProject>(".", std::vector<std::string>{});
    symbol_table_ = std::make_unique<SymbolTable>(project_.get());
    validator_ = std::make_unique<InterfaceValidator>(symbol_table_.get());
  }

  void TearDown() override {
    analyzers_.clear();
    validator_.reset();
    symbol_table_.reset();
    project_.reset();
  }

  // Helper to parse code and create validator
  void ParseCode(std::string_view code, std::string_view filename = "test.sv") {
    // Create and parse analyzer
    auto analyzer = std::make_unique<VerilogAnalyzer>(code, filename);
    absl::Status parse_status = analyzer->Analyze();
    // Ignore parse errors for test purposes
    
    // Add to project - this keeps ownership
    project_->UpdateFileContents(std::string(filename), analyzer.get());
    
    // Keep analyzer alive by storing it
    analyzers_.push_back(std::move(analyzer));
    
    // Build symbol table from this file
    std::vector<absl::Status> diagnostics;
    symbol_table_->BuildSingleTranslationUnit(filename, &diagnostics);
  }

  std::unique_ptr<VerilogProject> project_;
  std::unique_ptr<SymbolTable> symbol_table_;
  std::unique_ptr<InterfaceValidator> validator_;
  std::vector<std::unique_ptr<VerilogAnalyzer>> analyzers_;
};

// Basic Interface Tests

TEST_F(InterfaceValidatorTest, SimpleInterface) {
  // Test basic interface with signals
  constexpr std::string_view code = R"(
interface simple_intf;
  logic clk;
  logic [7:0] data;
endinterface

module test(simple_intf intf);
endmodule

module top;
  simple_intf bus();
  test t(.intf(bus));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllInterfaces();
  EXPECT_TRUE(status.ok()) << status.message();
  EXPECT_TRUE(validator_->GetErrors().empty());
}

TEST_F(InterfaceValidatorTest, EmptyInterface) {
  // Test empty interface (edge case)
  constexpr std::string_view code = R"(
interface empty_intf;
endinterface

module test(empty_intf intf);
endmodule

module top;
  empty_intf e();
  test t(.intf(e));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllInterfaces();
  EXPECT_TRUE(status.ok());
  EXPECT_TRUE(validator_->GetErrors().empty());
}

TEST_F(InterfaceValidatorTest, ParameterizedInterface) {
  // Test interface with parameters
  constexpr std::string_view code = R"(
interface param_intf #(parameter WIDTH = 8);
  logic [WIDTH-1:0] data;
endinterface

module test #(parameter W = 16)(param_intf #(.WIDTH(W)) intf);
endmodule

module top;
  param_intf #(.WIDTH(16)) bus();
  test #(.W(16)) t(.intf(bus));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllInterfaces();
  EXPECT_TRUE(status.ok());
  EXPECT_TRUE(validator_->GetErrors().empty());
}

// Modport Tests

TEST_F(InterfaceValidatorTest, BasicModport) {
  // Test basic modport with input/output
  constexpr std::string_view code = R"(
interface bus_intf;
  logic [7:0] data;
  logic valid;
  
  modport master (output data, output valid);
  modport slave (input data, input valid);
endinterface

module master_dev(bus_intf.master mst);
endmodule

module slave_dev(bus_intf.slave slv);
endmodule

module top;
  bus_intf bus();
  master_dev m(.mst(bus));
  slave_dev s(.slv(bus));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllInterfaces();
  EXPECT_TRUE(status.ok());
  EXPECT_TRUE(validator_->GetErrors().empty());
}

TEST_F(InterfaceValidatorTest, MultipleModports) {
  // Test interface with multiple modports
  constexpr std::string_view code = R"(
interface multi_intf;
  logic clk;
  logic [31:0] addr;
  logic [63:0] data;
  
  modport cpu (input clk, output addr, output data);
  modport memory (input clk, input addr, input data);
  modport monitor (input clk, input addr, input data);
endinterface

module cpu_unit(multi_intf.cpu c);
endmodule

module mem_unit(multi_intf.memory m);
endmodule

module mon_unit(multi_intf.monitor mon);
endmodule

module top;
  multi_intf bus();
  cpu_unit cpu(.c(bus));
  mem_unit mem(.m(bus));
  mon_unit mon(.mon(bus));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllInterfaces();
  EXPECT_TRUE(status.ok());
  EXPECT_TRUE(validator_->GetErrors().empty());
}

TEST_F(InterfaceValidatorTest, InoutModport) {
  // Test modport with inout signals
  constexpr std::string_view code = R"(
interface bidir_intf;
  wire [7:0] bidir_data;
  
  modport controller (inout bidir_data);
  modport device (inout bidir_data);
endinterface

module ctrl(bidir_intf.controller c);
endmodule

module dev(bidir_intf.device d);
endmodule

module top;
  bidir_intf bus();
  ctrl c(.c(bus));
  dev d(.d(bus));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllInterfaces();
  EXPECT_TRUE(status.ok());
  EXPECT_TRUE(validator_->GetErrors().empty());
}

// Connection Tests

TEST_F(InterfaceValidatorTest, DirectConnection) {
  // Test direct interface connection
  constexpr std::string_view code = R"(
interface data_intf;
  logic [15:0] data;
  logic valid;
endinterface

module source(data_intf out);
endmodule

module sink(data_intf in);
endmodule

module top;
  data_intf channel();
  source src(.out(channel));
  sink snk(.in(channel));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllInterfaces();
  EXPECT_TRUE(status.ok());
  EXPECT_TRUE(validator_->GetErrors().empty());
}

TEST_F(InterfaceValidatorTest, HierarchicalConnection) {
  // Test hierarchical interface connection
  constexpr std::string_view code = R"(
interface ctrl_intf;
  logic enable;
  logic [3:0] mode;
endinterface

module leaf(ctrl_intf ctrl);
endmodule

module middle(ctrl_intf ctrl);
  leaf l(.ctrl(ctrl));
endmodule

module top;
  ctrl_intf control();
  middle mid(.ctrl(control));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllInterfaces();
  EXPECT_TRUE(status.ok());
  EXPECT_TRUE(validator_->GetErrors().empty());
}

// Advanced Tests

TEST_F(InterfaceValidatorTest, InterfaceArray) {
  // Test array of interfaces
  constexpr std::string_view code = R"(
interface channel_intf;
  logic [7:0] data;
endinterface

module multi_channel(channel_intf ch[4]);
endmodule

module top;
  channel_intf channels[4]();
  multi_channel mc(.ch(channels));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllInterfaces();
  EXPECT_TRUE(status.ok());
  EXPECT_TRUE(validator_->GetErrors().empty());
}

TEST_F(InterfaceValidatorTest, GenericInterface) {
  // Test generic/type-parameterized interface
  constexpr std::string_view code = R"(
interface generic_intf #(parameter type T = logic [7:0]);
  T data;
  logic valid;
endinterface

module producer #(parameter type DT = logic [15:0])(
  generic_intf#(.T(DT)) prod
);
endmodule

module top;
  generic_intf#(.T(logic [31:0])) bus();
  producer#(.DT(logic [31:0])) p(.prod(bus));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllInterfaces();
  EXPECT_TRUE(status.ok());
  EXPECT_TRUE(validator_->GetErrors().empty());
}

// Error Tests

TEST_F(InterfaceValidatorTest, WrongModportDirection) {
  // Test invalid modport direction usage
  constexpr std::string_view code = R"(
interface dir_intf;
  logic [7:0] data;
  
  modport input_only (input data);
  modport output_only (output data);
endinterface

module writer(dir_intf.input_only intf);
  // Should detect: writing to input-only modport
  always_comb intf.data = 8'hFF;
endmodule

module top;
  dir_intf bus();
  writer w(.intf(bus));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllInterfaces();
  // Should detect error - writing to input modport
  // For now, just ensure it doesn't crash
  // TODO: Uncomment when implemented
  // EXPECT_FALSE(validator_->GetErrors().empty());
}

TEST_F(InterfaceValidatorTest, MissingModport) {
  // Test non-existent modport reference
  constexpr std::string_view code = R"(
interface test_intf;
  logic data;
  
  modport existing (input data);
endinterface

module user(test_intf.nonexistent intf);
endmodule

module top;
  test_intf bus();
  user u(.intf(bus));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllInterfaces();
  
  // Debug: Print what was found
  const auto& interfaces = validator_->GetInterfaces();
  std::cout << "Found " << interfaces.size() << " interfaces:" << std::endl;
  for (const auto& [name, info] : interfaces) {
    std::cout << "  Interface: " << name << " with " << info.modports.size() << " modports" << std::endl;
    for (const auto& mp : info.modports) {
      std::cout << "    Modport: " << mp.name << std::endl;
    }
  }
  
  const auto& errors = validator_->GetErrors();
  std::cout << "Found " << errors.size() << " errors:" << std::endl;
  for (const auto& error : errors) {
    std::cout << "  " << error << std::endl;
  }
  
  // Should detect error - nonexistent modport
  EXPECT_FALSE(validator_->GetErrors().empty());
  if (!validator_->GetErrors().empty()) {
    // Verify the error message mentions the missing modport
    const std::string& error = validator_->GetErrors()[0];
    EXPECT_NE(error.find("nonexistent"), std::string::npos);
    EXPECT_NE(error.find("Modport"), std::string::npos);
  }
}

}  // namespace
}  // namespace analysis
}  // namespace verilog

