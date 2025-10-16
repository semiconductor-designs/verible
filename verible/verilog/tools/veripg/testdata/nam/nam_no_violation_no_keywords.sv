// Copyright 2025 The Verible Authors.
// Negative test: No SystemVerilog keywords as identifiers - NO violation

module keyword_avoidance_example (
  input wire clk,
  input wire rst_n,
  input wire user_input,      // Not "input" as identifier
  input wire data_signal,     // Not "signal" keyword
  output logic result_output, // Not "output" as identifier
  output logic status_valid   // Not "valid" keyword conflict
);

  logic state_machine;    // Not "state" or "machine" keywords
  logic counter_value;    // Not "counter" keyword
  logic enable_flag;      // Not "enable" or "flag" keywords
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state_machine <= 1'b0;
      counter_value <= 1'b0;
      enable_flag <= 1'b0;
    end else begin
      state_machine <= user_input;
      counter_value <= data_signal;
      enable_flag <= 1'b1;
    end
  end
  
  assign result_output = state_machine;
  assign status_valid = enable_flag;

endmodule

