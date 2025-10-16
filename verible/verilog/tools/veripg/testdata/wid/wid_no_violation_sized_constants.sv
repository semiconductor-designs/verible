// Copyright 2025 The Verible Authors.
// Negative test: Properly sized constants - NO violation

module wid_no_violation_sized_constants (
  input wire clk,
  input wire rst_n,
  output logic [7:0] data_out1,
  output logic [15:0] data_out2,
  output logic [31:0] data_out3
);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_out1 <= 8'h00;      // 8-bit constant
      data_out2 <= 16'h0000;   // 16-bit constant
      data_out3 <= 32'h00000000; // 32-bit constant
    end else begin
      data_out1 <= 8'hFF;      // Properly sized
      data_out2 <= 16'hABCD;   // Properly sized
      data_out3 <= 32'h12345678; // Properly sized
    end
  end

endmodule

