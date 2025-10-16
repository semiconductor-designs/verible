// Copyright 2025 The Verible Authors.
// Edge case: Hierarchical reset distribution tree

module rst_edge_reset_tree (
  input wire clk,
  input wire global_rst_n,
  output logic module_rst_n,
  output logic local_rst_n
);

  // Reset tree: global -> module -> local
  // Each level adds one cycle of delay
  
  logic rst_sync1, rst_sync2;
  
  // Module-level reset (synchronized)
  always_ff @(posedge clk or negedge global_rst_n) begin
    if (!global_rst_n) begin
      rst_sync1 <= 1'b0;
      module_rst_n <= 1'b0;
    end else begin
      rst_sync1 <= 1'b1;
      module_rst_n <= rst_sync1;
    end
  end
  
  // Local reset (derived from module reset)
  always_ff @(posedge clk or negedge module_rst_n) begin
    if (!module_rst_n) begin
      rst_sync2 <= 1'b0;
      local_rst_n <= 1'b0;
    end else begin
      rst_sync2 <= 1'b1;
      local_rst_n <= rst_sync2;
    end
  end

endmodule

