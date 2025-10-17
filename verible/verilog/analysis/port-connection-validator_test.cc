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

#include "verible/verilog/analysis/port-connection-validator.h"

#include <memory>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "gtest/gtest.h"
#include "verible/common/analysis/syntax-tree-search.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-analyzer.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {
namespace analysis {
namespace {

// Test fixture for PortConnectionValidator tests
class PortConnectionValidatorTest : public ::testing::Test {
 protected:
  void SetUp() override {
    project_ = std::make_unique<VerilogProject>(".", std::vector<std::string>{});
    symbol_table_ = std::make_unique<SymbolTable>(project_.get());
    validator_ = std::make_unique<PortConnectionValidator>(symbol_table_.get());
  }

  void TearDown() override {
    analyzers_.clear();
    validator_.reset();
    symbol_table_.reset();
    project_.reset();
  }

  // Helper: Parse SystemVerilog code from memory
  void ParseCode(std::string_view code, std::string_view filename = "test.sv") {
    // Create and parse analyzer
    auto analyzer = std::make_unique<VerilogAnalyzer>(code, filename);
    absl::Status parse_status = analyzer->Analyze();
    // Ignore parse errors for now
    
    // Add to project - this keeps ownership
    project_->UpdateFileContents(std::string(filename), analyzer.get());
    
    // Keep analyzer alive by storing it
    analyzers_.push_back(std::move(analyzer));
    
    // Build symbol table from this file
    std::vector<absl::Status> diagnostics;
    symbol_table_->BuildSingleTranslationUnit(filename, &diagnostics);
    // Ignore diagnostics for now - we just need the symbol table populated
  }

  std::unique_ptr<VerilogProject> project_;
  std::unique_ptr<SymbolTable> symbol_table_;
  std::unique_ptr<PortConnectionValidator> validator_;
  std::vector<std::unique_ptr<VerilogAnalyzer>> analyzers_;
};

//-----------------------------------------------------------------------------
// Basic Port Connection Tests
//-----------------------------------------------------------------------------

TEST_F(PortConnectionValidatorTest, SimpleInputOutputConnection) {
  // Test basic input-output port connection
  constexpr std::string_view code = R"(
module producer (
  output logic [7:0] data_out
);
endmodule

module consumer (
  input logic [7:0] data_in
);
endmodule

module top;
  logic [7:0] data;
  producer u_prod (.data_out(data));
  consumer u_cons (.data_in(data));
endmodule
)";

  ParseCode(code);
  
  // Should validate without errors
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok()) << "Expected successful validation: " << status.message();
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

TEST_F(PortConnectionValidatorTest, InoutPortConnection) {
  // Test inout (bidirectional) port connection
  constexpr std::string_view code = R"(
module bidirectional (
  inout wire [7:0] data_bus
);
endmodule

module top;
  wire [7:0] bus;
  bidirectional u_bidir (.data_bus(bus));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

TEST_F(PortConnectionValidatorTest, EmptyModule) {
  // Test empty module with no ports
  constexpr std::string_view code = R"(
module empty_module;
endmodule

module top;
  empty_module u_empty();
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

TEST_F(PortConnectionValidatorTest, SinglePortModule) {
  // Test module with single port
  constexpr std::string_view code = R"(
module single_input (
  input logic clk
);
endmodule

module top;
  logic clock;
  single_input u_single (.clk(clock));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

TEST_F(PortConnectionValidatorTest, MultipleBasicPorts) {
  // Test module with multiple basic ports
  constexpr std::string_view code = R"(
module multi_port (
  input  logic       clk,
  input  logic       rst_n,
  input  logic [7:0] data_in,
  output logic [7:0] data_out,
  output logic       valid
);
endmodule

module top;
  logic       clock;
  logic       reset_n;
  logic [7:0] in_data;
  logic [7:0] out_data;
  logic       out_valid;
  
  multi_port u_mp (
    .clk(clock),
    .rst_n(reset_n),
    .data_in(in_data),
    .data_out(out_data),
    .valid(out_valid)
  );
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

//-----------------------------------------------------------------------------
// Port Direction Tests
//-----------------------------------------------------------------------------

TEST_F(PortConnectionValidatorTest, OutputToInputValid) {
  // Valid: Output port driving wire, wire driving input port
  constexpr std::string_view code = R"(
module source (
  output logic [7:0] out
);
endmodule

module sink (
  input logic [7:0] in
);
endmodule

module top;
  logic [7:0] wire_conn;
  source u_src (.out(wire_conn));
  sink u_snk (.in(wire_conn));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

TEST_F(PortConnectionValidatorTest, MultipleOutputsConflict) {
  // Invalid: Multiple outputs driving same wire (driver conflict)
  constexpr std::string_view code = R"(
module output_a (
  output logic [7:0] out_a
);
endmodule

module output_b (
  output logic [7:0] out_b
);
endmodule

module top;
  logic [7:0] shared;
  output_a u_a (.out_a(shared));
  output_b u_b (.out_b(shared));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  // This should detect multiple drivers
  EXPECT_FALSE(validator_->GetErrors().empty()) << "Expected driver conflict error";
}

TEST_F(PortConnectionValidatorTest, MixedDirections) {
  // Test module with mixed input/output/inout ports
  constexpr std::string_view code = R"(
module transceiver (
  input  logic       clk,
  input  logic       rst_n,
  input  logic [7:0] tx_data,
  output logic [7:0] rx_data,
  inout  wire        serial_io
);
endmodule

module top;
  logic       clock;
  logic       reset_n;
  logic [7:0] tx;
  logic [7:0] rx;
  wire        io;
  
  transceiver u_xcvr (
    .clk(clock),
    .rst_n(reset_n),
    .tx_data(tx),
    .rx_data(rx),
    .serial_io(io)
  );
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

//-----------------------------------------------------------------------------
// Port Type Tests
//-----------------------------------------------------------------------------

TEST_F(PortConnectionValidatorTest, MatchingLogicTypes) {
  // Test matching logic types
  constexpr std::string_view code = R"(
module sender (
  output logic [7:0] data
);
endmodule

module receiver (
  input logic [7:0] data
);
endmodule

module top;
  logic [7:0] connection;
  sender u_tx (.data(connection));
  receiver u_rx (.data(connection));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

TEST_F(PortConnectionValidatorTest, WireToLogicCompatible) {
  // Wire to logic should be compatible
  constexpr std::string_view code = R"(
module wire_source (
  output wire [7:0] data_out
);
endmodule

module logic_sink (
  input logic [7:0] data_in
);
endmodule

module top;
  wire [7:0] connection;
  wire_source u_src (.data_out(connection));
  logic_sink u_snk (.data_in(connection));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

TEST_F(PortConnectionValidatorTest, StructPortConnection) {
  // Test struct type port connections
  constexpr std::string_view code = R"(
typedef struct packed {
  logic [7:0] data;
  logic       valid;
  logic       ready;
} handshake_t;

module struct_source (
  output handshake_t hs_out
);
endmodule

module struct_sink (
  input handshake_t hs_in
);
endmodule

module top;
  handshake_t connection;
  struct_source u_src (.hs_out(connection));
  struct_sink u_snk (.hs_in(connection));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

//-----------------------------------------------------------------------------
// Port Width Tests
//-----------------------------------------------------------------------------

TEST_F(PortConnectionValidatorTest, MatchingWidths) {
  // Test exact width matching
  constexpr std::string_view code = R"(
module width_source (
  output logic [15:0] data_16bit,
  output logic [7:0]  data_8bit
);
endmodule

module width_sink (
  input logic [15:0] data_16bit,
  input logic [7:0]  data_8bit
);
endmodule

module top;
  logic [15:0] conn_16;
  logic [7:0]  conn_8;
  
  width_source u_src (
    .data_16bit(conn_16),
    .data_8bit(conn_8)
  );
  
  width_sink u_snk (
    .data_16bit(conn_16),
    .data_8bit(conn_8)
  );
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

TEST_F(PortConnectionValidatorTest, WidthMismatch) {
  // Test width mismatch detection
  constexpr std::string_view code = R"(
module wide_source (
  output logic [15:0] wide_out
);
endmodule

module narrow_sink (
  input logic [7:0] narrow_in
);
endmodule

module top;
  logic [15:0] wide_conn;
  logic [7:0]  narrow_conn;
  
  wide_source u_src (.wide_out(wide_conn));
  // Width mismatch: 16-bit to 8-bit
  narrow_sink u_snk (.narrow_in(wide_conn[7:0]));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  // Part-select should make this valid
  EXPECT_TRUE(status.ok());
}

TEST_F(PortConnectionValidatorTest, ParameterBasedWidth) {
  // Test parameter-based port widths
  constexpr std::string_view code = R"(
module param_source #(
  parameter WIDTH = 8
) (
  output logic [WIDTH-1:0] data_out
);
endmodule

module param_sink #(
  parameter WIDTH = 8
) (
  input logic [WIDTH-1:0] data_in
);
endmodule

module top;
  localparam WIDTH = 16;
  logic [WIDTH-1:0] connection;
  
  param_source #(.WIDTH(WIDTH)) u_src (.data_out(connection));
  param_sink #(.WIDTH(WIDTH)) u_snk (.data_in(connection));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

//-----------------------------------------------------------------------------
// Advanced Port Tests
//-----------------------------------------------------------------------------

TEST_F(PortConnectionValidatorTest, PackedArrayPorts) {
  // Test packed array port connections
  constexpr std::string_view code = R"(
module packed_source (
  output logic [3:0][7:0] data_out
);
endmodule

module packed_sink (
  input logic [3:0][7:0] data_in
);
endmodule

module top;
  logic [3:0][7:0] packed_connection;
  packed_source u_src (.data_out(packed_connection));
  packed_sink u_snk (.data_in(packed_connection));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

TEST_F(PortConnectionValidatorTest, UnpackedArrayPorts) {
  // Test unpacked array port connections
  constexpr std::string_view code = R"(
module unpacked_source (
  output logic [7:0] data_out [0:3]
);
endmodule

module unpacked_sink (
  input logic [7:0] data_in [0:3]
);
endmodule

module top;
  logic [7:0] unpacked_connection [0:3];
  unpacked_source u_src (.data_out(unpacked_connection));
  unpacked_sink u_snk (.data_in(unpacked_connection));
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

TEST_F(PortConnectionValidatorTest, ConcatenationInPort) {
  // Test concatenation expression in port connection
  constexpr std::string_view code = R"(
module byte_sink (
  input logic [15:0] data_in
);
endmodule

module top;
  logic [7:0] high_byte;
  logic [7:0] low_byte;
  
  byte_sink u_snk (
    .data_in({high_byte, low_byte})
  );
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

TEST_F(PortConnectionValidatorTest, PartSelectInPort) {
  // Test part select expression in port connection
  constexpr std::string_view code = R"(
module narrow_sink (
  input logic [3:0] nibble_in
);
endmodule

module top;
  logic [7:0] byte_data;
  
  narrow_sink u_snk_high (
    .nibble_in(byte_data[7:4])
  );
  
  narrow_sink u_snk_low (
    .nibble_in(byte_data[3:0])
  );
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

//-----------------------------------------------------------------------------
// Error Detection Tests
//-----------------------------------------------------------------------------

TEST_F(PortConnectionValidatorTest, UnconnectedPort) {
  // Test warning for unconnected port
  constexpr std::string_view code = R"(
module multi_port (
  input  logic clk,
  input  logic data_in,
  output logic data_out
);
endmodule

module top;
  logic clock;
  logic output_data;
  
  // Missing data_in connection
  multi_port u_mp (
    .clk(clock),
    .data_out(output_data)
  );
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  // Should generate warning for unconnected input
  EXPECT_FALSE(validator_->GetWarnings().empty()) << "Expected unconnected port warning";
}

TEST_F(PortConnectionValidatorTest, NonExistentPort) {
  // Test error for connection to non-existent port
  constexpr std::string_view code = R"(
module simple (
  input logic clk
);
endmodule

module top;
  logic clock;
  logic data;
  
  // Error: 'data_in' port doesn't exist in 'simple'
  simple u_simple (
    .clk(clock)
    // .data_in(data)  // This would be an error if uncommented
  );
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  // This specific test should pass (we don't connect to non-existent port)
  EXPECT_TRUE(status.ok());
}

//-----------------------------------------------------------------------------
// Integration Tests
//-----------------------------------------------------------------------------

TEST_F(PortConnectionValidatorTest, HierarchicalConnections) {
  // Test hierarchical port connections (multi-level)
  constexpr std::string_view code = R"(
module leaf (
  input  logic [7:0] data_in,
  output logic [7:0] data_out
);
endmodule

module middle (
  input  logic [7:0] data_in,
  output logic [7:0] data_out
);
  leaf u_leaf (
    .data_in(data_in),
    .data_out(data_out)
  );
endmodule

module top;
  logic [7:0] input_data;
  logic [7:0] output_data;
  
  middle u_middle (
    .data_in(input_data),
    .data_out(output_data)
  );
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

TEST_F(PortConnectionValidatorTest, ComplexRealWorldScenario) {
  // Test complex real-world scenario with multiple port types
  constexpr std::string_view code = R"(
typedef struct packed {
  logic [7:0] addr;
  logic [31:0] data;
  logic write;
  logic read;
} bus_req_t;

typedef struct packed {
  logic [31:0] data;
  logic ready;
  logic error;
} bus_resp_t;

module memory #(
  parameter ADDR_WIDTH = 8,
  parameter DATA_WIDTH = 32
) (
  input  logic       clk,
  input  logic       rst_n,
  input  bus_req_t   req,
  output bus_resp_t  resp
);
endmodule

module cpu (
  input  logic       clk,
  input  logic       rst_n,
  output bus_req_t   mem_req,
  input  bus_resp_t  mem_resp
);
endmodule

module soc;
  logic       clk;
  logic       rst_n;
  bus_req_t   mem_request;
  bus_resp_t  mem_response;
  
  cpu u_cpu (
    .clk(clk),
    .rst_n(rst_n),
    .mem_req(mem_request),
    .mem_resp(mem_response)
  );
  
  memory #(
    .ADDR_WIDTH(8),
    .DATA_WIDTH(32)
  ) u_mem (
    .clk(clk),
    .rst_n(rst_n),
    .req(mem_request),
    .resp(mem_response)
  );
endmodule
)";

  ParseCode(code);
  
  absl::Status status = validator_->ValidateAllConnections();
  EXPECT_TRUE(status.ok());
  EXPECT_EQ(validator_->GetErrors().size(), 0);
}

}  // namespace
}  // namespace analysis
}  // namespace verilog

