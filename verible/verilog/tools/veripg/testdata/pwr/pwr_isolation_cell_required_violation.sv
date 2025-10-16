// Test case for PWR_003: Isolation cell required for power-down domain
module pwr_isolation_cell_required_violation;
  // upf:power_domain PD_ALWAYS_ON
  logic enable;
  
  // upf:power_domain PD_SWITCHABLE
  // upf:can_power_down
  logic data_from_switchable;
  
  // PWR_003: Using signal from power-gated domain without isolation
  logic output_data;
  assign output_data = data_from_switchable;  // VIOLATION!
  
  // Should use isolation cell to clamp value when domain is off
endmodule

