// Test case: Function and task local variables
module function_unused_vars;
  
  function automatic int calculate(int a, int b);
    // WARNING: unused_local never used
    int unused_local;
    
    // WARNING: temp_val declared but not used
    int temp_val;
    
    // OK: result is used
    int result;
    result = a + b;
    return result;
  endfunction
  
  task process_values(input int x, input int y, output int z);
    // WARNING: task_unused never used
    int task_unused;
    
    // OK: task_temp is used
    int task_temp;
    task_temp = x * y;
    z = task_temp;
  endtask
  
endmodule

