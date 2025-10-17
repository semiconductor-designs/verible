// Test case: Multiple independent recursion cycles
module multiple_cycles;
  
  // Cycle 1: a1 -> a2 -> a1
  function automatic int func_a1(int x);
    if (x <= 0) return 0;
    return func_a2(x - 1);
  endfunction
  
  function automatic int func_a2(int x);
    if (x <= 0) return 1;
    return func_a1(x - 1);  // Cycle 1
  endfunction
  
  // Cycle 2: b1 -> b2 -> b1
  function automatic int func_b1(int x);
    if (x <= 0) return 10;
    return func_b2(x - 1);
  endfunction
  
  function automatic int func_b2(int x);
    if (x <= 0) return 11;
    return func_b1(x - 1);  // Cycle 2
  endfunction
  
  initial begin
    int r1, r2;
    r1 = func_a1(5);
    r2 = func_b1(3);
  end
  
endmodule

