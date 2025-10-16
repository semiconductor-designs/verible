// Test case: CDC_001 - Signal crosses clock domains without synchronizer
module cdc_violation_no_sync;
  logic clk_a, clk_b;
  logic data_a, data_b;
  
  // data_a is driven in clk_a domain
  always_ff @(posedge clk_a) begin
    data_a <= 1'b1;
  end
  
  // data_b uses data_a directly in clk_b domain - CDC violation!
  always_ff @(posedge clk_b) begin
    data_b <= data_a;  // CDC_001: Signal 'data_a' crosses from clk_a to clk_b without synchronizer
  end
endmodule

