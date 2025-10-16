// Copyright 2025 The Verible Authors.
// Negative test: Async set (not used as data) - NO violation

module rst_no_violation_async_set (
  input wire clk,
  input wire async_set_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Async set used for initialization (not as data signal)
  always_ff @(posedge clk or negedge async_set_n) begin
    if (!async_set_n)
      data_out <= 8'hFF;  // Set to all 1s
    else
      data_out <= data_in;
  end

endmodule

