// Port expression - concatenation

module byte_sink (
  input logic [15:0] data_in
);
endmodule

module top;
  logic [7:0] high_byte;
  logic [7:0] low_byte;
  
  // Concatenation in port connection
  byte_sink u_snk (
    .data_in({high_byte, low_byte})
  );
endmodule

