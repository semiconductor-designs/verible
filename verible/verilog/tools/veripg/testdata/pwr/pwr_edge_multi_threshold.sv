// Copyright 2025 The Verible Authors.
// Edge case: Multi-Vt (threshold voltage) cells

module pwr_edge_multi_threshold (
  input wire clk,
  input wire rst_n,
  input wire [7:0] critical_path_data,
  input wire [7:0] non_critical_data,
  output logic [7:0] fast_output,
  output logic [7:0] slow_output
);

  // Multi-Vt design: Mix of HVT, SVT, LVT cells
  // HVT (High-Vt): Low leakage, slow - use for non-critical paths
  // LVT (Low-Vt): High leakage, fast - use for critical paths
  // SVT (Standard-Vt): Balanced - use for most logic
  
  // Critical path: Use LVT cells (fast but leaky)
  logic [7:0] fast_pipeline_stage1;
  logic [7:0] fast_pipeline_stage2;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      fast_pipeline_stage1 <= 8'h00;
      fast_pipeline_stage2 <= 8'h00;
      fast_output <= 8'h00;
    end else begin
      fast_pipeline_stage1 <= critical_path_data;
      fast_pipeline_stage2 <= fast_pipeline_stage1 + 8'h01;
      fast_output <= fast_pipeline_stage2;
    end
  end
  
  // Non-critical path: Use HVT cells (slow but low-leakage)
  logic [7:0] slow_buffer;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      slow_buffer <= 8'h00;
      slow_output <= 8'h00;
    end else begin
      slow_buffer <= non_critical_data;
      slow_output <= slow_buffer;
    end
  end

endmodule

