// Copyright 2025 The Verible Authors.
// Edge case: Synchronous reset crossing domains (OK)

module cdc_edge_synchronous_reset_cdc (
  input wire clk_a,
  input wire clk_b,
  input wire sync_rst,  // Synchronous reset (not async)
  input wire data_in,
  output logic data_out
);

  // Synchronous reset crossing is OK (unlike async reset)
  logic sync_ff1, sync_ff2;
  
  always_ff @(posedge clk_b) begin
    if (sync_rst) begin
      sync_ff1 <= 1'b0;
      sync_ff2 <= 1'b0;
    end else begin
      sync_ff1 <= data_in;
      sync_ff2 <= sync_ff1;
    end
  end
  
  assign data_out = sync_ff2;

endmodule

