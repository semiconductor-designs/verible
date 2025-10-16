// Copyright 2025 The Verible Authors.
// Edge case: Async clear without clock in sensitivity list

module clk_edge_async_clear (
  input wire clk,
  input wire async_clear,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Async clear is in sensitivity list but not a clock
  always_ff @(posedge clk or posedge async_clear) begin
    if (async_clear)
      data_out <= 8'h00;
    else
      data_out <= data_in;
  end

endmodule

