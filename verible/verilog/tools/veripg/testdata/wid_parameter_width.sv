// Test file for WID_004: Parameter width inconsistent with usage

module wid_parameter_width #(
  parameter WIDTH = 8,
  parameter SIZE = 16
)(
  input wire [WIDTH-1:0] data_in,
  output logic [SIZE-1:0] data_out
);
  logic [WIDTH-1:0] temp;
  logic [7:0] fixed8;
  
  always_comb begin
    temp = data_in;      // OK: same width
    fixed8 = data_in;    // Violation if WIDTH > 8: parameter width inconsistent
    data_out = temp;     // Violation if WIDTH != SIZE: parameter width mismatch
  end
endmodule

