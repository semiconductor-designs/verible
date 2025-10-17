// Test file: Top module in 3-level hierarchy
// top -> mid_level -> leaf

module top (
  input logic clk,
  input logic rst_n,
  input logic [15:0] data_in,
  output logic [15:0] data_out
);
  
  logic [15:0] mid_to_top;
  
  mid_level u_mid (
    .clk(clk),
    .rst_n(rst_n),
    .data_in(data_in),
    .data_out(mid_to_top)
  );
  
  assign data_out = mid_to_top;
  
endmodule

