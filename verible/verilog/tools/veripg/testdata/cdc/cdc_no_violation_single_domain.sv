// Copyright 2025 The Verible Authors.
// Negative test: All signals in same clock domain - NO CDC, NO violations

module cdc_no_violation_single_domain (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out,
  output logic valid
);

  // All logic in same clock domain - no CDC issues
  logic [7:0] stage1, stage2, stage3;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      stage1 <= 8'h00;
      stage2 <= 8'h00;
      stage3 <= 8'h00;
      data_out <= 8'h00;
      valid <= 1'b0;
    end else begin
      stage1 <= data_in;
      stage2 <= stage1 + 8'h01;
      stage3 <= stage2 ^ 8'hAA;
      data_out <= stage3;
      valid <= 1'b1;
    end
  end

endmodule

