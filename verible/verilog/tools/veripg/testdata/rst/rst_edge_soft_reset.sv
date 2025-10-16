// Copyright 2025 The Verible Authors.
// Edge case: Software-controlled reset

module rst_edge_soft_reset (
  input wire clk,
  input wire hw_rst_n,
  input wire soft_rst,    // Software reset (register-based)
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Combination of hardware and software reset
  always_ff @(posedge clk or negedge hw_rst_n) begin
    if (!hw_rst_n || soft_rst)  // soft_rst is synchronous
      data_out <= 8'h00;
    else
      data_out <= data_in;
  end

endmodule

