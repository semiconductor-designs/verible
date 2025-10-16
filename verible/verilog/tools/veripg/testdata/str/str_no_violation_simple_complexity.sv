// Copyright 2025 The Verible Authors.
// Negative test: Low complexity module - NO violation

module str_no_violation_simple_complexity (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Simple module with low statement count
  logic [7:0] buffer;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      buffer <= 8'h00;
      data_out <= 8'h00;
    end else begin
      buffer <= data_in;
      data_out <= buffer;
    end
  end

endmodule

