// Test case: Functions that ARE called (should NOT be flagged)
module called_functions;
  
  // OK: All these functions are called
  function automatic int add(int a, int b);
    return a + b;
  endfunction
  
  function automatic int multiply(int a, int b);
    return a * b;
  endfunction
  
  function automatic int compute(int x);
    // Calls other functions
    int temp;
    temp = add(x, 10);
    return multiply(temp, 2);
  endfunction
  
  task display_result(input int value);
    // Task is called
    $display("Result: %d", value);
  endtask
  
  initial begin
    int result;
    result = compute(5);
    display_result(result);
  end
  
endmodule

