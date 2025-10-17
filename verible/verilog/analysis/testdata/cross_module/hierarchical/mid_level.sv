// Test file: Middle level in 3-level hierarchy

module mid_level (
  input logic clk,
  input logic rst_n,
  input logic [15:0] data_in,
  output logic [15:0] data_out
);
  
  logic [7:0] leaf_out_a, leaf_out_b;
  
  leaf u_leaf_a (
    .clk(clk),
    .rst_n(rst_n),
    .data_in(data_in[7:0]),
    .data_out(leaf_out_a)
  );
  
  leaf u_leaf_b (
    .clk(clk),
    .rst_n(rst_n),
    .data_in(data_in[15:8]),
    .data_out(leaf_out_b)
  );
  
  assign data_out = {leaf_out_b, leaf_out_a};
  
endmodule

