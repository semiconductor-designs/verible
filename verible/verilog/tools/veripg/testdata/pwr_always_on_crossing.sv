// Test file for PWR_005: Always-on signal crossing to power-gated domain

module pwr_always_on_crossing(
  input wire clk_aon,        // Always-on clock
  input wire clk_gated,      // Gated clock
  input wire data_aon,       // Always-on signal
  output logic data_gated
);
  // Violation: Always-on signal crosses to power-gated domain without proper handling
  logic internal_gated;
  
  // This logic is in power-gated domain
  always_ff @(posedge clk_gated) begin
    internal_gated <= data_aon;  // Violation: AON signal to gated domain
  end
  
  assign data_gated = internal_gated;
endmodule

module always_on_domain(
  input wire clk_aon,
  input wire data_in,
  output logic data_to_gated  // This crosses to gated domain
);
  always_ff @(posedge clk_aon) begin
    data_to_gated <= data_in;
  end
endmodule

