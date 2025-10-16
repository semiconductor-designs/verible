// Test case for RST_003: Mixed reset polarity
module rst_mixed_polarity_violation;
  logic clk, rst, rst_n, data1, data2;
  
  // RST_003: Mixed polarity - rst (active-high) and rst_n (active-low)
  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      data1 <= 1'b0;
    else
      data1 <= 1'b1;
  end
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      data2 <= 1'b0;
    else
      data2 <= 1'b1;
  end
endmodule

