// Test case for CLK_001: Missing clock signal in always_ff
module clk_missing_clock_violation;
  logic data;
  
  // CLK_001: always_ff without clock edge in sensitivity list
  // This should be always_comb or have @(posedge clk)
  always_ff begin
    data <= 1'b1;
  end
endmodule

