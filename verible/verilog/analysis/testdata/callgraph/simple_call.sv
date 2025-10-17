// Test case: Simple call - A calls B
module simple_call;
  
  function automatic int add_one(int x);
    return x + 1;
  endfunction
  
  function automatic int process(int x);
    // Function B calls Function A
    return add_one(x);
  endfunction
  
  initial begin
    int result;
    result = process(5);  // Entry point calls process
  end
  
endmodule

