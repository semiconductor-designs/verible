// Copyright 2025 The Verible Authors.
// Edge case: Async reset but same clock domain - Valid

module cdc_edge_async_reset_same_domain (
  input wire clk,
  input wire async_rst_n,  // Async reset, but same clock domain for data
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Async reset is OK when data stays in same clock domain
  always_ff @(posedge clk or negedge async_rst_n) begin
    if (!async_rst_n)
      data_out <= 8'h00;
    else
      data_out <= data_in;
  end

endmodule

