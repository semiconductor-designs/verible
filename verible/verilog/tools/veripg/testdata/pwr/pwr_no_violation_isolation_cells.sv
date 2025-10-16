// Copyright 2025 The Verible Authors.
// Negative test: Isolation cells present - NO violation

module isolation_cell (
  input wire signal_in,
  input wire iso_enable,
  output logic signal_out
);
  // Isolation cell: clamps output when domain is powered down
  assign signal_out = iso_enable ? 1'b0 : signal_in;
endmodule

module pwr_no_violation_isolation_cells (
  input wire clk_always_on,
  input wire clk_switchable,
  input wire rst_n,
  input wire power_domain_enable,
  input wire signal_from_switchable,
  output logic signal_to_always_on
);

  logic isolated_signal;
  
  // Isolation cell at power domain boundary
  isolation_cell u_iso_cell (
    .signal_in(signal_from_switchable),
    .iso_enable(!power_domain_enable),
    .signal_out(isolated_signal)
  );
  
  // Always-on domain logic
  always_ff @(posedge clk_always_on or negedge rst_n) begin
    if (!rst_n)
      signal_to_always_on <= 1'b0;
    else
      signal_to_always_on <= isolated_signal;
  end

endmodule

