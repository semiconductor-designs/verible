// Test case for CLK_001: Missing clock signal in always_ff
module clk_missing_clock_violation;
  logic clk, data;
  
  // CLK_001: always_ff without clock edge in sensitivity list
  // Has sensitivity list but missing posedge/negedge
  always_ff @(clk) begin
    data <= 1'b1;
  end
endmodule

