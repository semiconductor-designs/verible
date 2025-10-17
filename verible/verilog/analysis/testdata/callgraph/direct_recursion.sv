// Test case: Direct recursion - f() calls f()
module direct_recursion;
  
  function automatic int factorial(int n);
    if (n <= 1) begin
      return 1;
    end else begin
      // Direct recursion: factorial calls itself
      return n * factorial(n - 1);
    end
  endfunction
  
  initial begin
    int result;
    result = factorial(5);
  end
  
endmodule

