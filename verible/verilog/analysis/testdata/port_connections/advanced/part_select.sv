// Port expression - part select

module narrow_sink (
  input logic [3:0] nibble_in
);
endmodule

module top;
  logic [7:0] byte_data;
  
  // Part select in port connection
  narrow_sink u_snk_high (
    .nibble_in(byte_data[7:4])
  );
  
  narrow_sink u_snk_low (
    .nibble_in(byte_data[3:0])
  );
endmodule

