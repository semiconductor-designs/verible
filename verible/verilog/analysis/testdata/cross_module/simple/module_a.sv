// Test file: Simple cross-module reference
// module_a instantiates module_b

module module_a (
  input logic clk,
  input logic rst_n,
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  
  logic [7:0] intermediate;
  
  // Instantiate module_b
  module_b u_module_b (
    .clk(clk),
    .rst_n(rst_n),
    .data_in(data_in),
    .data_out(intermediate)
  );
  
  // Simple passthrough
  assign data_out = intermediate;
  
endmodule

