// Test case for CDC_002: Multi-bit signal crossing without Gray code
module cdc_multibit_violation;
  logic clk_a, clk_b;
  logic [7:0] data_a, data_b_sync, data_b;
  
  always_ff @(posedge clk_a) begin
    data_a <= 8'hFF;
  end
  
  always_ff @(posedge clk_b) begin
    data_b_sync <= data_a;  // CDC_002: Multi-bit crossing without Gray code
    data_b <= data_b_sync;
  end
endmodule

