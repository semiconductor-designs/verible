// Test case: Function calls multiple other functions
module multiple_calls;
  
  function automatic int add(int a, int b);
    return a + b;
  endfunction
  
  function automatic int multiply(int a, int b);
    return a * b;
  endfunction
  
  function automatic int compute(int x, int y);
    // Calls both add and multiply
    int sum, product;
    sum = add(x, y);
    product = multiply(x, y);
    return sum + product;
  endfunction
  
  initial begin
    int result;
    result = compute(3, 4);
  end
  
endmodule

