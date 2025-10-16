// Copyright 2025 The Verible Authors.
// Edge case: Width depends on parameter (dynamic)

module wid_edge_dynamic_width #(
  parameter int WIDTH = 8,
  parameter int MULTIPLIER = 2
)(
  input wire [WIDTH-1:0] data_in,
  output logic [(WIDTH*MULTIPLIER)-1:0] data_out
);

  // Width calculated from parameters
  always_comb begin
    data_out = {MULTIPLIER{data_in}};  // Replication
  end

endmodule

