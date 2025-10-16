// Copyright 2025 The Verible Authors.
// Negative test: Retention registers annotated - NO violation

module pwr_no_violation_retention (
  input wire clk,
  input wire rst_n,
  input wire save_enable,
  input wire restore_enable,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Retention register annotation (comment for UPF)
  // set_retention retention_rule -elements {state_register}
  logic [7:0] state_register;  // Marked for retention
  logic [7:0] shadow_register;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state_register <= 8'h00;
      shadow_register <= 8'h00;
    end else if (save_enable) begin
      shadow_register <= state_register;  // Save to retention
    end else if (restore_enable) begin
      state_register <= shadow_register;  // Restore from retention
    end else begin
      state_register <= data_in;
    end
  end
  
  assign data_out = state_register;

endmodule

