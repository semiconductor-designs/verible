// Copyright 2025 The Verible Authors.
// Edge case: 1-bit signals (minimum width boundary)

module wid_edge_1bit_to_1bit (
  input wire clk,
  input wire rst_n,
  input wire single_bit_in,
  output logic single_bit_out
);

  logic intermediate;
  
  // 1-bit = 1-bit (minimum width case)
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      intermediate <= 1'b0;
      single_bit_out <= 1'b0;
    end else begin
      intermediate <= single_bit_in;
      single_bit_out <= intermediate;
    end
  end

endmodule

