// Test case for STR_006: Instantiation without named ports
module sub_module(
  input logic clk,
  input logic data_in,
  output logic data_out
);
  assign data_out = data_in;
endmodule

module str_unnamed_ports_violation;
  logic clk, in_sig, out_sig;
  
  // STR_006: Positional ports instead of named ports
  sub_module u_sub(clk, in_sig, out_sig);  // VIOLATION!
  
  // Should use named ports:
  // sub_module u_sub(.clk(clk), .data_in(in_sig), .data_out(out_sig));
endmodule

