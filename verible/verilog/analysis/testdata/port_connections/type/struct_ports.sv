// Struct type port connections

typedef struct packed {
  logic [7:0] data;
  logic       valid;
  logic       ready;
} handshake_t;

module struct_source (
  output handshake_t hs_out
);
endmodule

module struct_sink (
  input handshake_t hs_in
);
endmodule

module top;
  handshake_t connection;
  
  struct_source u_src (.hs_out(connection));
  struct_sink u_snk (.hs_in(connection));
endmodule

