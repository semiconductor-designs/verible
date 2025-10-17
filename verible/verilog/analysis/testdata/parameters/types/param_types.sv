// Test: Different parameter types

module param_types #(
  parameter int         INT_PARAM = 42,
  parameter string      STR_PARAM = "hello",
  parameter real        REAL_PARAM = 3.14,
  parameter bit [7:0]   BIT_PARAM = 8'hAB,
  parameter logic [3:0] LOGIC_PARAM = 4'b1010
) (
  input  logic clk,
  output logic [7:0] data
);
  
  // Use parameters in various contexts
  initial begin
    $display("INT_PARAM = %d", INT_PARAM);
    $display("STR_PARAM = %s", STR_PARAM);
    $display("REAL_PARAM = %f", REAL_PARAM);
    $display("BIT_PARAM = %h", BIT_PARAM);
    $display("LOGIC_PARAM = %b", LOGIC_PARAM);
  end
  
  assign data = BIT_PARAM;
  
endmodule

module top;
  logic clk;
  logic [7:0] data;
  
  param_types #(
    .INT_PARAM(100),
    .STR_PARAM("world"),
    .REAL_PARAM(2.71),
    .BIT_PARAM(8'hFF),
    .LOGIC_PARAM(4'b0101)
  ) dut (
    .clk(clk),
    .data(data)
  );
endmodule

