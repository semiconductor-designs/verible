// Test file for PWR_003: Isolation cell required for power-down domain

module pwr_missing_isolation(
  input wire clk,
  input wire data_from_pd_domain,  // Violation: From power-down domain without isolation
  output logic data_out
);
  // data_from_pd_domain comes from a domain that can be powered down
  // Should have isolation cell to prevent X propagation
  
  logic internal_reg;
  
  always_ff @(posedge clk) begin
    internal_reg <= data_from_pd_domain;  // Direct connection is a violation
  end
  
  assign data_out = internal_reg;
endmodule

module power_down_domain(
  input wire clk_pd,
  input wire power_enable,
  input wire data_in,
  output logic data_out_pd  // This crosses to always-on domain
);
  // This domain can be powered down when power_enable is low
  always_ff @(posedge clk_pd) begin
    if (power_enable) begin
      data_out_pd <= data_in;
    end
  end
endmodule

