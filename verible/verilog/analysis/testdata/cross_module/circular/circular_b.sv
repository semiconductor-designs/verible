// Test file: Circular dependency (should be detected as error)
// circular_b instantiates circular_a (creates cycle)

module circular_b (
  input logic clk,
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  
  logic [7:0] from_a;
  
  // This creates a circular dependency
  circular_a u_a (
    .clk(clk),
    .data_in(data_in),
    .data_out(from_a)
  );
  
  assign data_out = from_a;
  
endmodule

