// Packed array port connections

module packed_source (
  output logic [3:0][7:0] data_out  // 4 bytes packed
);
endmodule

module packed_sink (
  input logic [3:0][7:0] data_in
);
endmodule

module top;
  logic [3:0][7:0] packed_connection;
  
  packed_source u_src (.data_out(packed_connection));
  packed_sink u_snk (.data_in(packed_connection));
endmodule

