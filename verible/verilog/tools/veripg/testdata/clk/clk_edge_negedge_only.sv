// Copyright 2025 The Verible Authors.
// Edge case: Negedge clocking (valid, less common)

module clk_edge_negedge_only (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Negedge clocking is valid (though less common than posedge)
  always_ff @(negedge clk or negedge rst_n) begin
    if (!rst_n)
      data_out <= 8'h00;
    else
      data_out <= data_in;
  end

endmodule

