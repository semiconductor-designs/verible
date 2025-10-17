// Simple port connection test - basic input/output ports

module producer (
  output logic [7:0] data_out,
  output logic       valid_out
);
endmodule

module consumer (
  input logic [7:0] data_in,
  input logic       valid_in
);
endmodule

// Valid connection: output to input
module top;
  logic [7:0] data;
  logic       valid;
  
  producer u_prod (
    .data_out(data),
    .valid_out(valid)
  );
  
  consumer u_cons (
    .data_in(data),
    .valid_in(valid)
  );
endmodule

