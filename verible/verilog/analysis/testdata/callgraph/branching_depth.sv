// Test case: Branching paths with different depths
module branching_depth;
  
  // Left branch: depth 3
  function automatic int left_deep(int x);
    return x + 1;
  endfunction
  
  function automatic int left_mid(int x);
    return left_deep(x) + 1;
  endfunction
  
  // Right branch: depth 1
  function automatic int right_shallow(int x);
    return x * 2;
  endfunction
  
  // Root calls both branches
  function automatic int root(int x);
    int l, r;
    l = left_mid(x);
    r = right_shallow(x);
    return l + r;
  endfunction
  
  initial begin
    int result;
    result = root(5);
  end
  
endmodule

