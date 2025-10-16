// Test case for PWR_005: Always-on signal crossing to power-gated domain
module pwr_always_on_crossing_violation;
  // upf:power_domain PD_ALWAYS_ON
  logic always_on_signal;
  
  // upf:power_domain PD_GATED
  logic gated_signal;
  
  // PWR_005: Always-on signal driving power-gated domain
  assign gated_signal = always_on_signal;  // VIOLATION!
  
  // Risk: gated domain may be off, causing X propagation
endmodule

