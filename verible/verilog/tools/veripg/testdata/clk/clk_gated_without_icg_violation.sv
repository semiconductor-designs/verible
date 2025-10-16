// Test case for CLK_004: Gated clock without ICG cell
module clk_gated_without_icg_violation;
  logic clk, enable, gated_clk, data;
  
  // CLK_004: Clock gating using combinational logic (should use ICG cell)
  assign gated_clk = clk & enable;
  
  always_ff @(posedge gated_clk) begin
    data <= 1'b1;
  end
endmodule

