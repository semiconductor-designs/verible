// Copyright 2025 The Verible Authors.
// Negative test: Single clock in always_ff - NO violation

module clk_no_violation_single_clock (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Single clock, properly used - no violation
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      data_out <= 8'h00;
    else
      data_out <= data_in;
  end

endmodule

