// Test case for PWR_004: Retention register without retention annotation
module pwr_retention_register_violation;
  // upf:power_domain PD_SWITCHABLE
  logic clk, rst_n;
  logic [7:0] state_register;  // PWR_004: Should have retention annotation
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      state_register <= 8'h00;
    else
      state_register <= state_register + 1;
  end
  
  // Should be annotated: // upf:retention
endmodule

