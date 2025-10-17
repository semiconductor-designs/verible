// Test: Hierarchical parameter usage and propagation

module leaf_module #(
  parameter SIZE = 4
) (
  input  logic [SIZE-1:0] in,
  output logic [SIZE-1:0] out
);
  assign out = ~in;
endmodule

module middle_module #(
  parameter WIDTH = 8
) (
  input  logic [WIDTH-1:0] data_in,
  output logic [WIDTH-1:0] data_out
);
  
  // Pass parameter down to leaf
  leaf_module #(.SIZE(WIDTH)) leaf (
    .in(data_in),
    .out(data_out)
  );
  
endmodule

module top;
  logic [15:0] in, out;
  
  // Parameter propagates: top -> middle (WIDTH=16) -> leaf (SIZE=16)
  middle_module #(.WIDTH(16)) mid (
    .data_in(in),
    .data_out(out)
  );
endmodule

