// Test case: No recursion - completely acyclic graph
module no_recursion;
  
  function automatic int leaf1(int x);
    return x + 1;
  endfunction
  
  function automatic int leaf2(int x);
    return x * 2;
  endfunction
  
  function automatic int middle(int x);
    return leaf1(x) + leaf2(x);
  endfunction
  
  function automatic int root(int x);
    return middle(x) + 10;
  endfunction
  
  initial begin
    int result;
    result = root(5);
  end
  
endmodule

