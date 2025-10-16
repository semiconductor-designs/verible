// Copyright 2025 The Verible Authors.
// Edge case: Wildcard port connections (.*)

module sub_module (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) data_out <= 8'h00;
    else data_out <= data_in;
  end
endmodule

module str_edge_wildcard_ports (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  output logic [7:0] data_out
);

  // Wildcard port connection - connects all matching signal names
  sub_module u_sub (.*);

endmodule

