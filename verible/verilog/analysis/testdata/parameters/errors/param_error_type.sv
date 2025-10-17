// Test: Error - parameter type mismatch

module typed_module #(
  parameter int INTEGER_PARAM = 10,
  parameter string STRING_PARAM = "test"
) (
  input  logic clk,
  output logic [7:0] data
);
  
  initial begin
    $display("INTEGER_PARAM = %d", INTEGER_PARAM);
    $display("STRING_PARAM = %s", STRING_PARAM);
  end
  
  assign data = INTEGER_PARAM[7:0];
  
endmodule

module top;
  logic clk;
  logic [7:0] data;
  
  // ERROR: Providing string where int expected, int where string expected
  typed_module #(
    .INTEGER_PARAM("wrong"),  // ERROR: string to int
    .STRING_PARAM(42)         // ERROR: int to string
  ) dut (
    .clk(clk),
    .data(data)
  );
endmodule

