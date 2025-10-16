// Copyright 2025 The Verible Authors.
// Negative test: Proper CDC handling - NO violations expected

module cdc_no_violation_proper_sync (
  input wire clk_a,
  input wire clk_b,
  input wire rst_n,
  input wire data_in,
  output logic data_out
);

  // Proper two-stage synchronizer for single-bit CDC
  logic sync_ff1, sync_ff2;
  
  always_ff @(posedge clk_b or negedge rst_n) begin
    if (!rst_n) begin
      sync_ff1 <= 1'b0;
      sync_ff2 <= 1'b0;
    end else begin
      sync_ff1 <= data_in;  // First stage
      sync_ff2 <= sync_ff1; // Second stage
    end
  end
  
  assign data_out = sync_ff2;

endmodule

