// Test case: Function calls itself (self-recursion)
module self_call;
  
  function automatic int count_down(int n);
    if (n <= 0) begin
      return 0;
    end else begin
      // Self-call: count_down calls count_down
      return n + count_down(n - 1);
    end
  endfunction
  
  initial begin
    int result;
    result = count_down(10);
  end
  
endmodule

