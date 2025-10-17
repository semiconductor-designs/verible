// Port width mismatch

module wide_source (
  output logic [15:0] wide_out
);
endmodule

module narrow_sink (
  input logic [7:0] narrow_in
);
endmodule

module top;
  logic [15:0] wide_conn;
  
  wide_source u_src (.wide_out(wide_conn));
  
  // Width mismatch: connecting 16-bit to 8-bit port
  // Should generate warning or error
  // narrow_sink u_snk (.narrow_in(wide_conn));
endmodule

