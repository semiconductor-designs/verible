// Copyright 2025 The Verible Authors.
// Negative test: UPPERCASE parameters - NO violation

module fifo_with_params #(
  parameter int DATA_WIDTH = 32,
  parameter int ADDR_WIDTH = 8,
  parameter int FIFO_DEPTH = 256,
  parameter bit ENABLE_BYPASS = 1'b0,
  parameter int MAX_BURST_SIZE = 16
)(
  input wire clk,
  input wire rst_n,
  input wire [DATA_WIDTH-1:0] write_data,
  output logic [DATA_WIDTH-1:0] read_data
);

  localparam int POINTER_WIDTH = ADDR_WIDTH;
  localparam bit ASYNC_RESET = 1'b1;
  
  logic [DATA_WIDTH-1:0] memory [FIFO_DEPTH-1:0];
  logic [POINTER_WIDTH-1:0] write_pointer;
  logic [POINTER_WIDTH-1:0] read_pointer;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      write_pointer <= '0;
      read_pointer <= '0;
    end
  end

endmodule

