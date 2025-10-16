// Copyright 2025 The Verible Authors.
// Edge case: Tristate buffers for CDC (rare but valid with external pull resistors)

module cdc_edge_tristate_buffer (
  input wire clk_a,
  input wire clk_b,
  input wire rst_n,
  input wire data_in_a,
  input wire enable_a,
  input wire enable_b,
  output logic data_out_b
);

  // Tristate buffer (external bus with pull-up/pull-down)
  wire shared_bus;
  
  // Driver from domain A
  logic data_a_reg;
  always_ff @(posedge clk_a or negedge rst_n) begin
    if (!rst_n)
      data_a_reg <= 1'b0;
    else
      data_a_reg <= data_in_a;
  end
  
  assign shared_bus = enable_a ? data_a_reg : 1'bz;
  
  // Receiver in domain B (with synchronizer)
  logic sync_ff1, sync_ff2;
  always_ff @(posedge clk_b or negedge rst_n) begin
    if (!rst_n) begin
      sync_ff1 <= 1'b0;
      sync_ff2 <= 1'b0;
    end else if (enable_b) begin
      sync_ff1 <= shared_bus;
      sync_ff2 <= sync_ff1;
    end
  end
  
  assign data_out_b = sync_ff2;

endmodule

