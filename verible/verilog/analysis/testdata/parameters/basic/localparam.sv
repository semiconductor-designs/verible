// Test: Local parameters cannot be overridden

module counter (
  input  logic clk,
  input  logic rst,
  output logic [7:0] count
);
  
  // Local parameter - cannot be overridden from outside
  localparam MAX_COUNT = 255;
  
  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      count <= 0;
    else if (count < MAX_COUNT)
      count <= count + 1;
    else
      count <= 0;
  end
  
endmodule

module top;
  logic clk, rst;
  logic [7:0] cnt;
  
  counter c (
    .clk(clk),
    .rst(rst),
    .count(cnt)
  );
endmodule

