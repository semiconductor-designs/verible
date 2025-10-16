// Copyright 2025 The Verible Authors.
// Negative test: Parameter widths consistent - NO violation

module wid_no_violation_parameter_consistent #(
  parameter int DATA_WIDTH = 32,
  parameter int ADDR_WIDTH = 16,
  parameter int COUNTER_WIDTH = 8
)(
  input wire clk,
  input wire rst_n,
  input wire [DATA_WIDTH-1:0] data_in,
  input wire [ADDR_WIDTH-1:0] addr_in,
  output logic [DATA_WIDTH-1:0] data_out,
  output logic [COUNTER_WIDTH-1:0] counter
);

  logic [DATA_WIDTH-1:0] data_buffer;
  logic [ADDR_WIDTH-1:0] addr_buffer;
  logic [COUNTER_WIDTH-1:0] internal_counter;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_buffer <= '0;
      addr_buffer <= '0;
      internal_counter <= '0;
    end else begin
      data_buffer <= data_in;          // Consistent with parameter
      addr_buffer <= addr_in;          // Consistent with parameter
      internal_counter <= internal_counter + 1'b1;
    end
  end
  
  assign data_out = data_buffer;
  assign counter = internal_counter;

endmodule

