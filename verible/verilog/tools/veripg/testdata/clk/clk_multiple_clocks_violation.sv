// Test case for CLK_002: Multiple clocks in single always block
module clk_multiple_clocks_violation;
  logic clk1, clk2, data;
  
  // CLK_002: Multiple clock edges in sensitivity list (violates single-clock domain rule)
  always_ff @(posedge clk1 or posedge clk2) begin
    data <= 1'b1;
  end
endmodule

