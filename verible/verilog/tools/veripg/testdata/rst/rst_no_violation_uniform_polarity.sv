// Copyright 2025 The Verible Authors.
// Negative test: All resets active-low (uniform polarity) - NO violation

module rst_no_violation_uniform_polarity (
  input wire clk,
  input wire rst_n,      // Active-low
  input wire clear_n,    // Active-low
  input wire [7:0] data_in,
  output logic [7:0] data_out,
  output logic [7:0] clear_out
);

  // All resets use same polarity (active-low)
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      data_out <= 8'h00;
    else
      data_out <= data_in;
  end
  
  always_ff @(posedge clk or negedge clear_n) begin
    if (!clear_n)
      clear_out <= 8'h00;
    else
      clear_out <= data_in;
  end

endmodule

