// Test case: Single function with no calls
module single_function;
  
  function automatic int identity(int x);
    return x;
  endfunction
  
  // Function exists but makes no calls
  
endmodule

