// Test: Parameter expressions and calculations

module calculator #(
  parameter BASE = 10,
  parameter MULTIPLIER = 2,
  parameter OFFSET = 5,
  // Derived parameters using expressions
  parameter RESULT = BASE * MULTIPLIER + OFFSET,  // 10 * 2 + 5 = 25
  parameter DOUBLE = BASE * 2,                     // 10 * 2 = 20
  parameter SHIFTED = BASE << 2                    // 10 << 2 = 40
) (
  input  logic [7:0] in,
  output logic [7:0] out1,
  output logic [7:0] out2,
  output logic [7:0] out3
);
  
  assign out1 = in + RESULT;
  assign out2 = in * DOUBLE;
  assign out3 = in + SHIFTED;
  
endmodule

module top;
  logic [7:0] in, out1, out2, out3;
  
  // Use default parameters
  calculator #(
    .BASE(8),
    .MULTIPLIER(3)
    // RESULT will be: 8 * 3 + 5 = 29
    // DOUBLE will be: 8 * 2 = 16
    // SHIFTED will be: 8 << 2 = 32
  ) dut (
    .in(in),
    .out1(out1),
    .out2(out2),
    .out3(out3)
  );
endmodule

