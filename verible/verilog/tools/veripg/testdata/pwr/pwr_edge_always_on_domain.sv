// Copyright 2025 The Verible Authors.
// Edge case: Always-on power domain (special handling)

module pwr_edge_always_on_domain (
  input wire clk_aon,  // Always-on clock
  input wire por_n,    // Power-on reset (never gated)
  input wire [7:0] config_data,
  output logic [7:0] aon_config_register
);

  // Always-on domain - never powered down
  // Used for wake-up logic, RTC, power management
  
  always_ff @(posedge clk_aon or negedge por_n) begin
    if (!por_n)
      aon_config_register <= 8'hAA;  // Default config
    else
      aon_config_register <= config_data;
  end

endmodule

