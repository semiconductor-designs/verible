// Test case: All functions are reachable from entry point
module all_reachable;
  
  function automatic int func_a(int x);
    return x + 1;
  endfunction
  
  function automatic int func_b(int x);
    return x + 2;
  endfunction
  
  function automatic int func_c(int x);
    return func_a(x) + func_b(x);
  endfunction
  
  initial begin
    int result;
    result = func_c(5);  // Calls func_a and func_b
  end
  
  // All three functions are reachable from initial block
  
endmodule

