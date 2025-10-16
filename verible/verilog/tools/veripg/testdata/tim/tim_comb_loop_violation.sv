// Test case for TIM_001: Combinational loop detected
module tim_comb_loop_violation;
  logic a, b, c;
  
  // TIM_001: Combinational loop - a depends on b, b depends on a
  assign a = b & c;
  assign b = a | c;
endmodule

