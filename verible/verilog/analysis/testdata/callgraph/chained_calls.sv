// Test case: Chained calls - A -> B -> C
module chained_calls;
  
  function automatic int func_c(int x);
    return x + 1;
  endfunction
  
  function automatic int func_b(int x);
    return func_c(x) + 2;
  endfunction
  
  function automatic int func_a(int x);
    return func_b(x) + 3;
  endfunction
  
  initial begin
    int result;
    result = func_a(10);  // A -> B -> C chain
  end
  
endmodule

