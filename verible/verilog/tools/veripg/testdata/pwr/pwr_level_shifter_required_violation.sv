// Test case for PWR_002: Level shifter required at domain boundary
// Signal crossing from one power domain to another needs level shifter

module pwr_level_shifter_required_violation;
  // upf:power_domain PD_LOW
  logic signal_low_voltage;
  
  // upf:power_domain PD_HIGH
  logic signal_high_voltage;
  
  // PWR_002: Direct assignment across power domains without level shifter
  assign signal_high_voltage = signal_low_voltage;  // VIOLATION!
  
  // Should use level shifter cell instead
endmodule

