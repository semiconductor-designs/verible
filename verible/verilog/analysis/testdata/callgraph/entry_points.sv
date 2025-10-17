// Test case: Multiple entry points (no callers)
module entry_points;
  
  // Entry point 1: Called only from initial block
  function automatic int entry1(int x);
    return x + 10;
  endfunction
  
  // Entry point 2: Also called only from initial block
  function automatic int entry2(int x);
    return x * 3;
  endfunction
  
  // Not an entry point: called by helper
  function automatic int helper_func(int x);
    return x + 1;
  endfunction
  
  // Entry point 3: Calls helper_func
  function automatic int entry3(int x);
    return helper_func(x) + 5;
  endfunction
  
  initial begin
    int r1, r2, r3;
    r1 = entry1(5);
    r2 = entry2(7);
    r3 = entry3(9);
  end
  
endmodule

