// Test case: Indirect recursion - f() -> g() -> f()
module indirect_recursion;
  
  function automatic int func_f(int x);
    if (x <= 0) begin
      return 0;
    end else begin
      return func_g(x - 1);  // f calls g
    end
  endfunction
  
  function automatic int func_g(int x);
    if (x <= 0) begin
      return 1;
    end else begin
      return func_f(x - 1);  // g calls f (cycle!)
    end
  endfunction
  
  initial begin
    int result;
    result = func_f(10);
  end
  
endmodule

