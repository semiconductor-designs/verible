// Copyright 2025 The Verible Authors.
// Edge case: Very wide signals (512-bit - practical maximum)

module wid_edge_max_width (
  input wire clk,
  input wire rst_n,
  input wire [511:0] ultra_wide_in,
  output logic [511:0] ultra_wide_out
);

  logic [511:0] buffer_stage1;
  logic [511:0] buffer_stage2;
  
  // 512-bit operations (large but valid)
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      buffer_stage1 <= 512'h0;
      buffer_stage2 <= 512'h0;
      ultra_wide_out <= 512'h0;
    end else begin
      buffer_stage1 <= ultra_wide_in;
      buffer_stage2 <= buffer_stage1;
      ultra_wide_out <= buffer_stage2;
    end
  end

endmodule

