// Test file for STR_001: Module has no ports (should be testbench)

module str_module_no_ports;  // Violation: No ports - should be explicitly marked as testbench
  logic clk;
  logic rst_n;
  logic [7:0] data;
  
  // Internal logic without ports suggests this might be a testbench
  // but it's not named with _tb suffix
  
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
  
  initial begin
    rst_n = 0;
    #20 rst_n = 1;
  end
endmodule

