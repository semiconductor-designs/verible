// Copyright 2025 The Verible Authors.
// Negative test: Well-structured module - NO violation

// Module header: Purpose, interfaces, author
// Author: Test Suite
// Date: 2025-01-16
// Description: Example of proper module structure

module str_no_violation_good_structure (
  // Clock and reset (proper ordering)
  input wire clk,
  input wire rst_n,
  
  // Input signals
  input wire [7:0] data_in,
  input wire valid_in,
  
  // Output signals
  output logic [7:0] data_out,
  output logic valid_out
);

  // Internal signals
  logic [7:0] internal_buffer;
  
  // Sequential logic
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      internal_buffer <= 8'h00;
      data_out <= 8'h00;
      valid_out <= 1'b0;
    end else begin
      internal_buffer <= data_in;
      data_out <= internal_buffer;
      valid_out <= valid_in;
    end
  end

endmodule

