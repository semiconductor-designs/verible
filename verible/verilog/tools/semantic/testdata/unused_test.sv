// Test file for unused entity detection
module unused_test;
  reg used_signal;
  reg unused_signal;  // Should be detected as unused
  
  wire used_wire;
  wire unused_wire;   // Should be detected as unused
  
  assign used_wire = used_signal;
  
  function int used_function(int x);
    return x + 1;
  endfunction
  
  function int unused_function(int x);  // Should be detected as unused
    return x * 2;
  endfunction
  
  initial begin
    used_signal = 1'b0;
    used_signal = used_function(5);
  end
endmodule

