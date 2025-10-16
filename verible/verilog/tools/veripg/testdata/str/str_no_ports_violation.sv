// Test case for STR_001: Module has no ports (should be testbench)
// STR_001: Module with no ports should be marked as testbench

module str_no_ports_violation;  // VIOLATION: no ports, not marked as tb
  logic clk, data;
  
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
endmodule

// Good: testbench naming convention
module good_testbench_tb;
  logic clk, data;
  
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
endmodule

