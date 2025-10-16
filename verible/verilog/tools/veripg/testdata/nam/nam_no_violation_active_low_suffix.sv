// Copyright 2025 The Verible Authors.
// Negative test: _n suffix for active-low - NO violation

module active_low_signals (
  input wire clk,
  input wire rst_n,
  input wire chip_select_n,
  input wire write_enable_n,
  input wire output_enable_n,
  input wire interrupt_n,
  output logic ready_n,
  output logic error_n
);

  logic internal_state;
  
  // All active-low signals properly suffixed with _n
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      ready_n <= 1'b1;      // Active-low, so 1 = not ready
      error_n <= 1'b1;      // Active-low, so 1 = no error
      internal_state <= 1'b0;
    end else if (!chip_select_n && !write_enable_n) begin
      ready_n <= 1'b0;      // Assert ready (active-low)
      internal_state <= 1'b1;
    end
  end

endmodule

