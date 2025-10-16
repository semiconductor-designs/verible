// Test file for WID_005: Port width mismatch in instantiation

module sub_module #(
  parameter WIDTH = 8
)(
  input wire [WIDTH-1:0] data_in,
  output logic [WIDTH-1:0] data_out
);
  assign data_out = data_in;
endmodule

module wid_port_instantiation;
  logic [7:0] data8;
  logic [15:0] data16;
  logic [7:0] out8;
  logic [15:0] out16;
  
  // OK: Matching widths
  sub_module #(.WIDTH(8)) u1 (
    .data_in(data8),
    .data_out(out8)
  );
  
  // Violation: Port width mismatch
  sub_module #(.WIDTH(8)) u2 (
    .data_in(data16),  // 16-bit connected to 8-bit port
    .data_out(out16)   // 8-bit port connected to 16-bit signal
  );
endmodule

