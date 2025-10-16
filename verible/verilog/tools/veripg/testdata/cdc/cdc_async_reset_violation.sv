// Test case for CDC_004: Async reset crossing clock domains
module cdc_async_reset_violation;
  logic clk_a, clk_b;
  logic async_rst;  // Async reset in one domain
  logic data_a, data_b;
  
  // Domain A: Uses async_rst
  always_ff @(posedge clk_a or negedge async_rst) begin
    if (!async_rst)
      data_a <= 1'b0;
    else
      data_a <= 1'b1;
  end
  
  // Domain B: Also uses async_rst without synchronization
  // CDC_004: Async reset crossing domains - needs synchronizer
  always_ff @(posedge clk_b or negedge async_rst) begin
    if (!async_rst)
      data_b <= 1'b0;
    else
      data_b <= data_a;
  end
endmodule

