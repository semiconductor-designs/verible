// Test file for PWR_001: Missing power domain annotation

module pwr_missing_domain_annotation(
  input wire clk,
  input wire rst_n,
  input wire data_in,
  output logic data_out
);
  // Violation: No power domain annotation (should have // synopsys dc_script_begin or UPF pragma)
  // In a real power-aware design, this module should declare its power domain
  
  logic internal_reg;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      internal_reg <= 1'b0;
    end else begin
      internal_reg <= data_in;
    end
  end
  
  assign data_out = internal_reg;
endmodule

