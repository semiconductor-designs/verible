// Copyright 2025 The Verible Authors.
// Edge case: Mux in data path (not clock path) - Valid, no violation

module cdc_edge_mux_data_path (
  input wire clk,
  input wire rst_n,
  input wire sel,
  input wire [7:0] data_a,
  input wire [7:0] data_b,
  output logic [7:0] data_out
);

  // Mux selecting data (not clock) - this is fine
  logic [7:0] selected_data;
  
  always_comb begin
    selected_data = sel ? data_a : data_b;
  end
  
  // Register the muxed data
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      data_out <= 8'h00;
    else
      data_out <= selected_data;
  end

endmodule

