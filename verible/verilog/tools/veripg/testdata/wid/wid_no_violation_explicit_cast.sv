// Copyright 2025 The Verible Authors.
// Negative test: Explicit width casting - NO violation

module wid_no_violation_explicit_cast (
  input wire clk,
  input wire rst_n,
  input wire [15:0] wide_data,
  input wire [3:0] narrow_data,
  output logic [7:0] data_out1,
  output logic [15:0] data_out2
);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_out1 <= 8'h00;
      data_out2 <= 16'h0000;
    end else begin
      // Explicit casting prevents width mismatch issues
      data_out1 <= wide_data[7:0];           // Explicit truncation
      data_out2 <= {12'h000, narrow_data};   // Explicit extension
    end
  end

endmodule

