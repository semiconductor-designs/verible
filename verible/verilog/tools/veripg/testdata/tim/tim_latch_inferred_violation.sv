// Test case for TIM_002: Latch inferred (incomplete if/case)
module tim_latch_inferred_violation;
  logic sel, a, b, out;
  
  // TIM_002: Latch inferred - incomplete if (no else clause)
  always_comb begin
    if (sel)
      out = a;
    // Missing else - creates latch!
  end
endmodule

