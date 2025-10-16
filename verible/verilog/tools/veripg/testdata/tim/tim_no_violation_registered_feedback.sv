// Copyright 2025 The Verible Authors.
// Negative test: Feedback through register (no comb loop) - NO violation

module tim_no_violation_registered_feedback (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Feedback loop broken by register - no combinational loop
  logic [7:0] feedback_reg;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      feedback_reg <= 8'h00;
      data_out <= 8'h00;
    end else begin
      feedback_reg <= data_out + data_in;  // Feedback through register
      data_out <= feedback_reg;
    end
  end

endmodule

