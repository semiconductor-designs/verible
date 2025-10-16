// Copyright 2025 The Verible Authors.
// Negative test: Single power domain (no crossing) - NO violation

module pwr_no_violation_single_domain (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // All logic in same power domain - no power intent issues
  logic [7:0] pipeline_stage1;
  logic [7:0] pipeline_stage2;
  logic [7:0] pipeline_stage3;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      pipeline_stage1 <= 8'h00;
      pipeline_stage2 <= 8'h00;
      pipeline_stage3 <= 8'h00;
      data_out <= 8'h00;
    end else begin
      pipeline_stage1 <= data_in;
      pipeline_stage2 <= pipeline_stage1;
      pipeline_stage3 <= pipeline_stage2;
      data_out <= pipeline_stage3;
    end
  end

endmodule

