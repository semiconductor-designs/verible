// Copyright 2025 The Verible Authors.
// Negative test: All widths match - NO violation

module wid_no_violation_matching_widths (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out,
  output logic [15:0] wide_out
);

  logic [7:0] buffer1;
  logic [7:0] buffer2;
  logic [15:0] wide_buffer;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      buffer1 <= 8'h00;
      buffer2 <= 8'h00;
      wide_buffer <= 16'h0000;
      data_out <= 8'h00;
      wide_out <= 16'h0000;
    end else begin
      buffer1 <= data_in;           // 8-bit = 8-bit ✓
      buffer2 <= buffer1;            // 8-bit = 8-bit ✓
      data_out <= buffer2;           // 8-bit = 8-bit ✓
      wide_buffer <= {buffer1, buffer2};  // 16-bit = {8,8} ✓
      wide_out <= wide_buffer;       // 16-bit = 16-bit ✓
    end
  end

endmodule

