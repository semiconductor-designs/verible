// Test file for PWR_002: Level shifter required at domain boundary

module low_voltage_domain(
  input wire clk_low,
  input wire data_from_high,  // Violation: Signal from high voltage domain without level shifter
  output logic data_out_low
);
  // This module operates at low voltage (e.g., 0.9V)
  // data_from_high comes from a high voltage domain (e.g., 1.8V)
  // Should have level shifter instantiation
  
  always_ff @(posedge clk_low) begin
    data_out_low <= data_from_high;  // Direct connection is a violation
  end
endmodule

module high_voltage_domain(
  input wire clk_high,
  input wire data_in,
  output logic data_to_low  // This will cross to low voltage domain
);
  always_ff @(posedge clk_high) begin
    data_to_low <= data_in;
  end
endmodule

