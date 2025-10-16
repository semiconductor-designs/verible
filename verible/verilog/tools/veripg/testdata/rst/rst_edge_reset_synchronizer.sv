// Copyright 2025 The Verible Authors.
// Edge case: Reset synchronizer itself

module rst_edge_reset_synchronizer (
  input wire clk,
  input wire async_rst_n,
  output logic sync_rst_n
);

  // Reset synchronizer: converts async reset to sync
  // This is a special case - the synchronizer for reset signal itself
  
  logic rst_sync1;
  
  always_ff @(posedge clk or negedge async_rst_n) begin
    if (!async_rst_n) begin
      rst_sync1 <= 1'b0;
      sync_rst_n <= 1'b0;
    end else begin
      rst_sync1 <= 1'b1;
      sync_rst_n <= rst_sync1;
    end
  end

endmodule

