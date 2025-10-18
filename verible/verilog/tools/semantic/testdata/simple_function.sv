module example;
  function automatic int add(int a, int b);
    return a + b;
  endfunction
  
  function automatic int double_add(int x, int y);
    return add(add(x, y), add(x, y));
  endfunction
  
  function automatic int triple_add(int m, int n);
    return add(double_add(m, n), m);
  endfunction
endmodule
