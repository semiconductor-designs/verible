// Copyright 2025 The Verible Authors.
// Edge case: Nested power hierarchy

module pwr_edge_nested_domains (
  input wire clk,
  input wire rst_n,
  input wire pd_l1_enable,
  input wire pd_l2_enable,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Power hierarchy: Always-on > L1 > L2
  // L2 can only be on if L1 is on
  // L1 can only be on if Always-on is on
  
  logic [7:0] l1_data;
  logic [7:0] l2_data;
  
  // Level 1 power domain
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      l1_data <= 8'h00;
    else if (pd_l1_enable)
      l1_data <= data_in;
  end
  
  // Level 2 power domain (nested within L1)
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      l2_data <= 8'h00;
    else if (pd_l1_enable && pd_l2_enable)
      l2_data <= l1_data;
  end
  
  assign data_out = l2_data;

endmodule

