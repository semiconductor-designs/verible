// Test case for WID_005: Port width mismatch in instantiation
module sub_module(
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  assign data_out = data_in;
endmodule

module wid_port_mismatch_violation;
  logic [15:0] wide_data;
  logic [7:0] narrow_data;
  
  // WID_005: Port width mismatch - connecting 16-bit signal to 8-bit port
  sub_module u_sub(
    .data_in(wide_data),      // Mismatch: 16-bit to 8-bit port
    .data_out(narrow_data)
  );
endmodule

