// Copyright 2025 The Verible Authors.
// Negative test: PLL-generated clocks - NO violation

module clk_no_violation_pll_output (
  input wire clk_in,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out_fast,
  output logic [7:0] data_out_slow
);

  // PLL generates multiple clocks from single input
  wire clk_fast, clk_slow;
  wire pll_locked;
  
  pll u_pll (
    .clk_in(clk_in),
    .rst_n(rst_n),
    .clk_fast(clk_fast),    // 2x clock
    .clk_slow(clk_slow),    // 0.5x clock
    .locked(pll_locked)
  );
  
  // Use fast clock
  always_ff @(posedge clk_fast or negedge rst_n) begin
    if (!rst_n)
      data_out_fast <= 8'h00;
    else if (pll_locked)
      data_out_fast <= data_in;
  end
  
  // Use slow clock
  always_ff @(posedge clk_slow or negedge rst_n) begin
    if (!rst_n)
      data_out_slow <= 8'h00;
    else if (pll_locked)
      data_out_slow <= data_in;
  end

endmodule

// Simplified PLL model
module pll (
  input wire clk_in,
  input wire rst_n,
  output wire clk_fast,
  output wire clk_slow,
  output logic locked
);
  assign clk_fast = clk_in;  // Simplified
  assign clk_slow = clk_in;  // Simplified
  
  always_ff @(posedge clk_in or negedge rst_n) begin
    if (!rst_n)
      locked <= 1'b0;
    else
      locked <= 1'b1;
  end
endmodule

