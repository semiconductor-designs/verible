// Bidirectional ports with multiple drivers (legal)
module bidirectional_port (
  inout logic bidir,
  input logic oe,
  input logic data_out,
  output logic data_in
);
  
  // OK: Multiple drivers on inout port (legal)
  assign bidir = oe ? data_out : 1'bz;
  assign data_in = bidir;
  
endmodule

