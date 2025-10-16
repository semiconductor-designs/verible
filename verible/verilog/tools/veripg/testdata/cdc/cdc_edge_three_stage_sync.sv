// Copyright 2025 The Verible Authors.
// Edge case: 3-stage synchronizer (over-engineered but valid)

module cdc_edge_three_stage_sync (
  input wire clk_src,
  input wire clk_dst,
  input wire rst_n,
  input wire data_in,
  output logic data_out
);

  // Three-stage synchronizer for extra margin (valid, no violation)
  logic sync_ff1, sync_ff2, sync_ff3;
  
  always_ff @(posedge clk_dst or negedge rst_n) begin
    if (!rst_n) begin
      sync_ff1 <= 1'b0;
      sync_ff2 <= 1'b0;
      sync_ff3 <= 1'b0;
    end else begin
      sync_ff1 <= data_in;
      sync_ff2 <= sync_ff1;
      sync_ff3 <= sync_ff2;  // Extra stage for high-speed designs
    end
  end
  
  assign data_out = sync_ff3;

endmodule

