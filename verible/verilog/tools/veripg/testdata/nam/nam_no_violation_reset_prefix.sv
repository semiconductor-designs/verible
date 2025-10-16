// Copyright 2025 The Verible Authors.
// Negative test: rst_ and rstn_ prefixes - NO violation

module reset_domain_example (
  input wire clk,
  input wire rst_n,          // Active-low async reset
  input wire rst_sync,       // Synchronous reset
  input wire rstn_power,     // Power domain reset
  input wire rst_debug,      // Debug reset
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // All reset signals properly named with rst_ or rstn_
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n || rst_sync)
      data_out <= 8'h00;
    else
      data_out <= data_in;
  end

endmodule

