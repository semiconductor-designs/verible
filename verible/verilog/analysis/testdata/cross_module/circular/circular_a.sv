// Test file: Circular dependency (should be detected as error)
// circular_a instantiates circular_b

module circular_a (
  input logic clk,
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  
  logic [7:0] from_b;
  
  // This creates a circular dependency
  circular_b u_b (
    .clk(clk),
    .data_in(data_in),
    .data_out(from_b)
  );
  
  assign data_out = from_b;
  
endmodule

