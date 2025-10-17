// Test: Parameter override in module instantiation

module register #(
  parameter WIDTH = 8
) (
  input  logic             clk,
  input  logic             rst,
  input  logic [WIDTH-1:0] d,
  output logic [WIDTH-1:0] q
);
  
  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      q <= '0;
    else
      q <= d;
  end
  
endmodule

module top;
  logic clk, rst;
  logic [7:0]  d8, q8;
  logic [15:0] d16, q16;
  logic [31:0] d32, q32;
  
  // Use default WIDTH=8
  register reg8 (
    .clk(clk),
    .rst(rst),
    .d(d8),
    .q(q8)
  );
  
  // Override WIDTH to 16
  register #(.WIDTH(16)) reg16 (
    .clk(clk),
    .rst(rst),
    .d(d16),
    .q(q16)
  );
  
  // Override WIDTH to 32
  register #(.WIDTH(32)) reg32 (
    .clk(clk),
    .rst(rst),
    .d(d32),
    .q(q32)
  );
endmodule

