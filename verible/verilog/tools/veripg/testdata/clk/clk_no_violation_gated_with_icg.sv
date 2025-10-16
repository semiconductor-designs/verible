// Copyright 2025 The Verible Authors.
// Negative test: Properly gated clock with ICG cell - NO violation

module clk_no_violation_gated_with_icg (
  input wire clk,
  input wire rst_n,
  input wire enable,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Instantiate ICG (Integrated Clock Gating) cell
  wire clk_gated;
  
  // ICG cell instantiation (proper clock gating)
  icg_cell u_icg (
    .clk_in(clk),
    .enable(enable),
    .clk_out(clk_gated)
  );
  
  // Use gated clock
  always_ff @(posedge clk_gated or negedge rst_n) begin
    if (!rst_n)
      data_out <= 8'h00;
    else
      data_out <= data_in;
  end

endmodule

// ICG cell module (vendor-provided or custom)
module icg_cell (
  input wire clk_in,
  input wire enable,
  output wire clk_out
);
  logic enable_latched;
  
  always_latch begin
    if (!clk_in)
      enable_latched <= enable;
  end
  
  assign clk_out = clk_in & enable_latched;
endmodule

