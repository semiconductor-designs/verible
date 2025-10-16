// Copyright 2025 The Verible Authors.
// Negative test: Synchronous reset properly used - NO violation

module rst_no_violation_sync_reset (
  input wire clk,
  input wire sync_rst,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Synchronous reset - proper usage
  always_ff @(posedge clk) begin
    if (sync_rst)
      data_out <= 8'h00;
    else
      data_out <= data_in;
  end

endmodule

