// Copyright 2025 The Verible Authors.
// Edge case: Conditional reset (with enable)

module rst_edge_conditional_reset (
  input wire clk,
  input wire rst_n,
  input wire reset_enable,  // Reset only applies when enabled
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Conditional reset - only resets when enabled
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n && reset_enable)
      data_out <= 8'h00;
    else if (!rst_n && !reset_enable)
      data_out <= data_out;  // Hold value
    else
      data_out <= data_in;
  end

endmodule

