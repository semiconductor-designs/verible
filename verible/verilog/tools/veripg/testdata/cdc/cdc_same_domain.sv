// Test case: No CDC - Both signals in same clock domain
module cdc_same_domain;
  logic clk;
  logic data_a, data_b;
  
  // Both signals in same clk domain - no CDC issue
  always_ff @(posedge clk) begin
    data_a <= 1'b1;
  end
  
  always_ff @(posedge clk) begin
    data_b <= data_a;  // No CDC violation - same domain
  end
endmodule

