// Test case for CDC_003: Clock used in data path (clock muxing)
module cdc_clock_mux_violation;
  logic clk_a, clk_b, sel;
  logic mux_clk;
  logic data;
  
  // CDC_003: Clock muxing - using clocks in data path
  assign mux_clk = sel ? clk_a : clk_b;
  
  always_ff @(posedge mux_clk) begin
    data <= 1'b1;
  end
endmodule

