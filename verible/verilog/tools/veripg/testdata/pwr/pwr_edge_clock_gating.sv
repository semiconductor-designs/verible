// Copyright 2025 The Verible Authors.
// Edge case: Clock gating for power savings

module clock_gate_cell (
  input wire clk_in,
  input wire enable,
  output logic clk_out
);
  logic enable_latched;
  always_latch begin
    if (!clk_in)
      enable_latched <= enable;
  end
  assign clk_out = clk_in & enable_latched;
endmodule

module pwr_edge_clock_gating (
  input wire clk,
  input wire rst_n,
  input wire module_enable,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  logic clk_gated;
  
  // Clock gating for power reduction
  clock_gate_cell u_cg (
    .clk_in(clk),
    .enable(module_enable),
    .clk_out(clk_gated)
  );
  
  // Logic clocked by gated clock
  always_ff @(posedge clk_gated or negedge rst_n) begin
    if (!rst_n)
      data_out <= 8'h00;
    else
      data_out <= data_in;
  end

endmodule

