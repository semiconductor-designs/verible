// Test: Error - attempting to override localparam

module counter_with_max #(
  parameter INIT_VALUE = 0
) (
  input  logic clk,
  input  logic rst,
  output logic [7:0] count
);
  
  // This is a localparam and CANNOT be overridden
  localparam MAX_VALUE = 100;
  
  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      count <= INIT_VALUE;
    else if (count < MAX_VALUE)
      count <= count + 1;
    else
      count <= INIT_VALUE;
  end
  
endmodule

module top;
  logic clk, rst;
  logic [7:0] cnt;
  
  // ERROR: Attempting to override MAX_VALUE which is a localparam
  counter_with_max #(
    .INIT_VALUE(10),
    .MAX_VALUE(200)  // ERROR: Cannot override localparam
  ) dut (
    .clk(clk),
    .rst(rst),
    .count(cnt)
  );
endmodule

