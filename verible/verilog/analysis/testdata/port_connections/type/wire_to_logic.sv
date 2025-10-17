// Wire to logic connection (valid in SystemVerilog)

module wire_source (
  output wire [7:0] data_out
);
endmodule

module logic_sink (
  input logic [7:0] data_in
);
endmodule

module top;
  wire [7:0] connection;
  
  // Valid: wire and logic are compatible
  wire_source u_src (.data_out(connection));
  logic_sink u_snk (.data_in(connection));
endmodule

