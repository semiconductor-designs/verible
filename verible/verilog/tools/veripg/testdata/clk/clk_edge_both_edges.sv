// Copyright 2025 The Verible Authors.
// Edge case: Both clock edges (DDR - valid with documentation)

module clk_edge_both_edges (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out_pos,
  output logic [7:0] data_out_neg
);

  // DDR (Double Data Rate) - sample on both edges
  // This is valid for high-speed interfaces when properly documented
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      data_out_pos <= 8'h00;
    else
      data_out_pos <= data_in;
  end
  
  always_ff @(negedge clk or negedge rst_n) begin
    if (!rst_n)
      data_out_neg <= 8'h00;
    else
      data_out_neg <= data_in;
  end

endmodule

