// Test: Basic parameter declaration and usage

module adder #(
  parameter WIDTH = 8
) (
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  output logic [WIDTH-1:0] sum
);
  
  assign sum = a + b;
  
endmodule

module top;
  logic [7:0] x, y, result;
  
  // Use default WIDTH=8
  adder dut (
    .a(x),
    .b(y),
    .sum(result)
  );
endmodule

