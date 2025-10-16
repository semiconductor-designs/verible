// Copyright 2025 The Verible Authors.
// Edge case: Partial state reset (subset of flip-flops)

module rst_edge_partial_reset (
  input wire clk,
  input wire full_rst_n,
  input wire partial_rst,
  input wire [7:0] data_in,
  output logic [7:0] control_regs,
  output logic [7:0] data_regs
);

  // Full reset resets everything
  // Partial reset only resets control registers
  
  always_ff @(posedge clk or negedge full_rst_n) begin
    if (!full_rst_n) begin
      control_regs <= 8'h00;
      data_regs <= 8'h00;
    end else if (partial_rst) begin
      control_regs <= 8'h00;  // Reset control only
      data_regs <= data_regs;  // Preserve data
    end else begin
      control_regs <= data_in;
      data_regs <= data_in;
    end
  end

endmodule

