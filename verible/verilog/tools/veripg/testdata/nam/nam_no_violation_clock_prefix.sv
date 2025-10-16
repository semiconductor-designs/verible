// Copyright 2025 The Verible Authors.
// Negative test: clk_ prefix for clocks - NO violation

module multi_clock_domain (
  input wire clk_fast,
  input wire clk_slow,
  input wire clk_peripheral,
  input wire clk_debug,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out_fast,
  output logic [7:0] data_out_slow
);

  // All clock signals properly prefixed with clk_
  always_ff @(posedge clk_fast or negedge rst_n) begin
    if (!rst_n)
      data_out_fast <= 8'h00;
    else
      data_out_fast <= data_in;
  end
  
  always_ff @(posedge clk_slow or negedge rst_n) begin
    if (!rst_n)
      data_out_slow <= 8'h00;
    else
      data_out_slow <= data_in;
  end

endmodule

