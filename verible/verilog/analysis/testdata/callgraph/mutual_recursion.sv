// Test case: Mutual recursion - A calls B, B calls A
module mutual_recursion;
  
  function automatic int is_even(int n);
    if (n == 0) begin
      return 1;
    end else begin
      return is_odd(n - 1);  // even calls odd
    end
  endfunction
  
  function automatic int is_odd(int n);
    if (n == 0) begin
      return 0;
    end else begin
      return is_even(n - 1);  // odd calls even (mutual recursion!)
    end
  endfunction
  
  initial begin
    int r1, r2;
    r1 = is_even(10);
    r2 = is_odd(11);
  end
  
endmodule

