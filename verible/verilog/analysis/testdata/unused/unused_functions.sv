// Test case: Unused functions and tasks
module unused_functions;
  
  // WARNING: unused_function is never called
  function automatic int unused_function(int a);
    return a + 1;
  endfunction
  
  // WARNING: unused_task is never called
  task unused_task(input int x, output int y);
    y = x * 2;
  endtask
  
  // OK: called_function is used
  function automatic int called_function(int a);
    return a + 10;
  endfunction
  
  // OK: called_task is used
  task called_task(input int x, output int y);
    y = x + 5;
  endtask
  
  initial begin
    int result;
    result = called_function(5);
    called_task(10, result);
  end
  
endmodule

