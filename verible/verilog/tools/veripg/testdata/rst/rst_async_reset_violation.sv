// Test case for RST_002: Asynchronous reset not properly synchronized
module rst_async_reset_violation;
  logic clk, async_rst_n, data;
  
  // RST_002: Using async reset (negedge) - should recommend sync reset release
  always_ff @(posedge clk or negedge async_rst_n) begin
    if (!async_rst_n)
      data <= 1'b0;
    else
      data <= 1'b1;
  end
endmodule

