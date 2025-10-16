// Test case for RST_001: Missing reset in sequential logic
module rst_missing_reset_violation;
  logic clk, data;
  
  // RST_001: always_ff without reset (no reset in sensitivity list, no reset logic inside)
  always_ff @(posedge clk) begin
    data <= 1'b1;
  end
endmodule

