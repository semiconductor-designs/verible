// Test case: Multiple CDC violations in one module
module cdc_multiple_violations;
  logic clk_a, clk_b, clk_c;
  logic sig_a1, sig_a2, sig_b1, sig_c1;
  
  // Signals in clk_a domain
  always_ff @(posedge clk_a) begin
    sig_a1 <= 1'b0;
    sig_a2 <= 1'b1;
  end
  
  // sig_b1 uses sig_a1 - CDC violation #1
  always_ff @(posedge clk_b) begin
    sig_b1 <= sig_a1;  // CDC_001: sig_a1 crosses clk_a -> clk_b
  end
  
  // sig_c1 uses sig_a2 - CDC violation #2
  always_ff @(posedge clk_c) begin
    sig_c1 <= sig_a2;  // CDC_001: sig_a2 crosses clk_a -> clk_c
  end
endmodule

