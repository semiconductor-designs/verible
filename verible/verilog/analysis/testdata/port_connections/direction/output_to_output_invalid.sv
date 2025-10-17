// Invalid: Multiple outputs driving same wire (driver conflict)

module output_a (
  output logic [7:0] out_a
);
endmodule

module output_b (
  output logic [7:0] out_b
);
endmodule

module top;
  logic [7:0] shared;
  
  // Invalid: Multiple drivers on same wire
  output_a u_a (.out_a(shared));
  output_b u_b (.out_b(shared));
endmodule

