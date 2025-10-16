// Copyright 2025 The Verible Authors.
// Negative test: Level shifters at boundaries - NO violation

module level_shifter_cell (
  input wire signal_in,
  output logic signal_out
);
  // Level shifter implementation (simplified)
  assign signal_out = signal_in;
endmodule

module pwr_no_violation_level_shifters (
  input wire clk_low_voltage,
  input wire clk_high_voltage,
  input wire rst_n,
  input wire signal_from_low_voltage,
  output logic signal_to_high_voltage
);

  logic shifted_signal;
  
  // Level shifter at power domain boundary
  level_shifter_cell u_ls_low_to_high (
    .signal_in(signal_from_low_voltage),
    .signal_out(shifted_signal)
  );
  
  // High voltage domain logic
  always_ff @(posedge clk_high_voltage or negedge rst_n) begin
    if (!rst_n)
      signal_to_high_voltage <= 1'b0;
    else
      signal_to_high_voltage <= shifted_signal;
  end

endmodule

