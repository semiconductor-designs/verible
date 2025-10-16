// Test case for PWR_001: Missing power domain annotation
// UPF-aware check: modules should have power domain annotations

module pwr_missing_power_domain_violation (
  input logic clk,
  input logic data_in,
  output logic data_out
);
  // PWR_001: Missing power domain annotation
  // Should have: // upf:power_domain PD_CORE or similar comment
  
  always_ff @(posedge clk) begin
    data_out <= data_in;
  end
endmodule

// Good example with annotation
module good_power_domain (
  input logic clk,
  input logic data_in,
  output logic data_out
);
  // upf:power_domain PD_CORE
  
  always_ff @(posedge clk) begin
    data_out <= data_in;
  end
endmodule

