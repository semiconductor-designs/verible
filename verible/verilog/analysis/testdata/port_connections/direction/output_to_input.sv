// Valid: Output port connected to input port (through wire)

module source (
  output logic [7:0] out
);
endmodule

module sink (
  input logic [7:0] in
);
endmodule

module top;
  logic [7:0] wire_conn;
  
  // Valid: output drives wire, wire drives input
  source u_src (.out(wire_conn));
  sink u_snk (.in(wire_conn));
endmodule

