// Copyright 2025 The Verible Authors.
// Negative test: Clock enable signal (not clock as data) - NO violation

module clk_no_violation_derived_enable (
  input wire clk,
  input wire rst_n,
  input wire enable,  // Clock enable, not clock signal
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Clock used as clock, enable as enable - correct usage
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      data_out <= 8'h00;
    else if (enable)  // Enable signal, not clock
      data_out <= data_in;
  end

endmodule

