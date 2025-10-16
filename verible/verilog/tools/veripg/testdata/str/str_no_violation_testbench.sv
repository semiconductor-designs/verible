// Copyright 2025 The Verible Authors.
// Negative test: Testbench with no ports (allowed) - NO violation

module str_no_violation_testbench;
  // Testbenches typically have no ports - this is acceptable
  
  logic clk;
  logic rst_n;
  logic [7:0] test_data;
  
  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
  
  // Reset generation
  initial begin
    rst_n = 0;
    #20 rst_n = 1;
  end
  
  // Test stimulus
  initial begin
    test_data = 8'h00;
    wait(rst_n);
    #100;
    test_data = 8'hAA;
    #100;
    test_data = 8'h55;
    #100;
    $finish;
  end

endmodule

