// Copyright 2025 The Verible Authors.
// Negative test: Async reset properly synchronized - NO violation

module rst_no_violation_async_reset (
  input wire clk,
  input wire async_rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Async reset properly used in sensitivity list
  always_ff @(posedge clk or negedge async_rst_n) begin
    if (!async_rst_n)
      data_out <= 8'h00;
    else
      data_out <= data_in;
  end

endmodule

