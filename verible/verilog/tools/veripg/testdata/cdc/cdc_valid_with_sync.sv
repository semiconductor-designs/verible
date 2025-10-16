// Test case: Valid CDC - Signal has proper 2-stage synchronizer
module cdc_valid_with_sync;
  logic clk_a, clk_b;
  logic data_a, data_b;
  logic data_b_sync1, data_b_sync2;
  
  // data_a is driven in clk_a domain
  always_ff @(posedge clk_a) begin
    data_a <= 1'b1;
  end
  
  // Proper 2-stage synchronizer in clk_b domain
  always_ff @(posedge clk_b) begin
    data_b_sync1 <= data_a;      // Stage 1
    data_b_sync2 <= data_b_sync1; // Stage 2
    data_b <= data_b_sync2;       // Final use
  end
endmodule

