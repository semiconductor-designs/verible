// Test: Array parameters

module lut #(
  parameter int LUT_SIZE = 4,
  parameter logic [7:0] LUT_VALUES [0:3] = '{8'h00, 8'h55, 8'hAA, 8'hFF}
) (
  input  logic [1:0] index,
  output logic [7:0] value
);
  
  assign value = LUT_VALUES[index];
  
endmodule

module top;
  logic [1:0] idx;
  logic [7:0] val;
  
  // Override with custom LUT values
  lut #(
    .LUT_SIZE(4),
    .LUT_VALUES('{8'h10, 8'h20, 8'h30, 8'h40})
  ) lut_inst (
    .index(idx),
    .value(val)
  );
endmodule

