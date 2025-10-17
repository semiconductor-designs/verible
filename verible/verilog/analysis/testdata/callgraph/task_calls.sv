// Test case: Task call graph
module task_calls;
  
  task task_a(input int x, output int y);
    y = x + 10;
  endtask
  
  task task_b(input int x, output int y);
    int temp;
    task_a(x, temp);  // Task B calls Task A
    y = temp * 2;
  endtask
  
  initial begin
    int result;
    task_b(5, result);
  end
  
endmodule

