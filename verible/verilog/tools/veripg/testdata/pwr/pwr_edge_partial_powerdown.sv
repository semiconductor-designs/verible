// Copyright 2025 The Verible Authors.
// Edge case: Partial module power-down

module pwr_edge_partial_powerdown (
  input wire clk,
  input wire rst_n,
  input wire enable_accelerator,
  input wire [31:0] data_in,
  output logic [31:0] basic_output,
  output logic [31:0] accelerated_output
);

  // Always-on: Basic functionality
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      basic_output <= 32'h0;
    else
      basic_output <= data_in;
  end
  
  // Power-gated: Accelerator (optional, high-power)
  logic [31:0] accel_stage1, accel_stage2;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      accel_stage1 <= 32'h0;
      accel_stage2 <= 32'h0;
      accelerated_output <= 32'h0;
    end else if (enable_accelerator) begin
      accel_stage1 <= data_in * 2;
      accel_stage2 <= accel_stage1 + 32'h100;
      accelerated_output <= accel_stage2;
    end
  end

endmodule

