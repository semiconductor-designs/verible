// Copyright 2025 The Verible Authors.
// Negative test: Shallow hierarchy (<=5 levels) - NO violation

module level5 (input wire clk, output logic out);
  always_ff @(posedge clk) out <= 1'b1;
endmodule

module level4 (input wire clk, output logic out);
  level5 u5 (.clk(clk), .out(out));
endmodule

module level3 (input wire clk, output logic out);
  level4 u4 (.clk(clk), .out(out));
endmodule

module level2 (input wire clk, output logic out);
  level3 u3 (.clk(clk), .out(out));
endmodule

module level1 (input wire clk, output logic out);
  level2 u2 (.clk(clk), .out(out));
endmodule

// Top-level: Total depth = 5 (within limit)
module str_no_violation_shallow_hierarchy (
  input wire clk,
  output logic out
);
  level1 u1 (.clk(clk), .out(out));
endmodule

