// Port width using parameters

module param_source #(
  parameter WIDTH = 8
) (
  output logic [WIDTH-1:0] data_out
);
endmodule

module param_sink #(
  parameter WIDTH = 8
) (
  input logic [WIDTH-1:0] data_in
);
endmodule

module top;
  localparam WIDTH = 16;
  logic [WIDTH-1:0] connection;
  
  // Both instantiated with same WIDTH parameter
  param_source #(.WIDTH(WIDTH)) u_src (.data_out(connection));
  param_sink #(.WIDTH(WIDTH)) u_snk (.data_in(connection));
endmodule

