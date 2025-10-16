// Copyright 2025 The Verible Authors.
// Edge case: 3+ power domains with proper isolation

module pwr_edge_multiple_domains (
  input wire clk_core,
  input wire clk_dsp,
  input wire clk_memory,
  input wire rst_n,
  input wire [31:0] data_in,
  output logic [31:0] data_out
);

  // Power Domain 1: Core processing
  logic [31:0] core_data;
  always_ff @(posedge clk_core or negedge rst_n) begin
    if (!rst_n) core_data <= 32'h0;
    else core_data <= data_in;
  end
  
  // Power Domain 2: DSP accelerator
  logic [31:0] dsp_data;
  always_ff @(posedge clk_dsp or negedge rst_n) begin
    if (!rst_n) dsp_data <= 32'h0;
    else dsp_data <= core_data;
  end
  
  // Power Domain 3: Memory controller
  logic [31:0] memory_data;
  always_ff @(posedge clk_memory or negedge rst_n) begin
    if (!rst_n) memory_data <= 32'h0;
    else memory_data <= dsp_data;
  end
  
  assign data_out = memory_data;

endmodule

