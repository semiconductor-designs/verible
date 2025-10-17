// Test case: Unreachable function (never called)
module unreachable_function;
  
  // This function is NEVER called - unreachable!
  function automatic int unreachable(int x);
    return x + 100;
  endfunction
  
  // This function IS called
  function automatic int reachable(int x);
    return x + 1;
  endfunction
  
  initial begin
    int result;
    result = reachable(10);
    // unreachable() is never called - should be detected
  end
  
endmodule

