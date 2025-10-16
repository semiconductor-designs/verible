// Copyright 2025 The Verible Authors.
// Negative test: Long but descriptive names - NO violation

module transaction_processing_controller (
  input wire system_clock,
  input wire asynchronous_reset_n,
  input wire transaction_valid,
  input wire [31:0] transaction_identifier,
  output logic transaction_acknowledged,
  output logic [31:0] processed_transaction_result
);

  logic transaction_processing_complete;
  logic [31:0] intermediate_calculation_buffer;
  
  always_ff @(posedge system_clock or negedge asynchronous_reset_n) begin
    if (!asynchronous_reset_n) begin
      transaction_processing_complete <= 1'b0;
      intermediate_calculation_buffer <= 32'h0;
      processed_transaction_result <= 32'h0;
    end else if (transaction_valid) begin
      intermediate_calculation_buffer <= transaction_identifier + 32'h1;
      processed_transaction_result <= intermediate_calculation_buffer;
      transaction_processing_complete <= 1'b1;
    end
  end
  
  assign transaction_acknowledged = transaction_processing_complete;

endmodule

