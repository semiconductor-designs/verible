// Unpacked array port connections

module unpacked_source (
  output logic [7:0] data_out [0:3]  // Array of 4 bytes
);
endmodule

module unpacked_sink (
  input logic [7:0] data_in [0:3]
);
endmodule

module top;
  logic [7:0] unpacked_connection [0:3];
  
  unpacked_source u_src (.data_out(unpacked_connection));
  unpacked_sink u_snk (.data_in(unpacked_connection));
endmodule

