// Test: Error - module requires parameter but none provided

module strict_module #(
  parameter WIDTH  // No default value - must be provided
) (
  input  logic [WIDTH-1:0] in,
  output logic [WIDTH-1:0] out
);
  assign out = in;
endmodule

module top;
  logic [7:0] data_in, data_out;
  
  // ERROR: WIDTH parameter has no default and must be specified
  strict_module inst (
    .in(data_in),
    .out(data_out)
  );
  // Should have been: strict_module #(.WIDTH(8)) inst (...)
endmodule

