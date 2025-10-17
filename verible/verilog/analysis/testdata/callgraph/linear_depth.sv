// Test case: Linear call depth - A -> B -> C
module linear_depth;
  
  function automatic int depth3(int x);
    return x + 1;
  endfunction
  
  function automatic int depth2(int x);
    return depth3(x) + 1;
  endfunction
  
  function automatic int depth1(int x);
    return depth2(x) + 1;
  endfunction
  
  // Entry point at depth 0
  initial begin
    int result;
    result = depth1(10);  // Depth: 0 -> 1 -> 2 -> 3
  end
  
endmodule

