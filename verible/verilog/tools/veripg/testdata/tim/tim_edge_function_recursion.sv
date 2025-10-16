// Copyright 2025 The Verible Authors.
// Edge case: Function recursion (not a combinational loop in synthesis)

module tim_edge_function_recursion (
  input wire [7:0] n,
  output logic [15:0] factorial
);

  // Recursive function - not a combinational loop for synthesis
  // (synthesis tools will unroll or report error)
  function automatic [15:0] calc_factorial(input [7:0] num);
    if (num <= 8'h01)
      return 16'h0001;
    else
      return num * calc_factorial(num - 1);
  endfunction
  
  assign factorial = calc_factorial(n);

endmodule

