// Constant propagation analysis
module constant_propagation (
  input  logic a,
  output logic result1,
  output logic result2
);
  
  // Parameters are constants
  localparam CONST_VAL = 8'h5A;
  localparam CONST_ZERO = 1'b0;
  
  // Constant assignments
  logic const_signal;
  assign const_signal = CONST_ZERO;  // const_signal is constant
  
  // Mixed constant and variable
  logic [7:0] mixed;
  assign mixed = CONST_VAL;  // mixed is constant
  
  assign result1 = const_signal;  // result1 driven by constant
  assign result2 = a | const_signal;  // result2 driven by constant and variable
  
endmodule

