// Test case: Long recursion cycle - f() -> g() -> h() -> f()
module long_cycle;
  
  function automatic int func_f(int x);
    if (x <= 0) return 0;
    return func_g(x - 1);
  endfunction
  
  function automatic int func_g(int x);
    if (x <= 0) return 1;
    return func_h(x - 1);
  endfunction
  
  function automatic int func_h(int x);
    if (x <= 0) return 2;
    return func_f(x - 1);  // Cycle back to f
  endfunction
  
  initial begin
    int result;
    result = func_f(9);
  end
  
endmodule

