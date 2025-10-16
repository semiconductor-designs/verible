// Test case for WID_004: Parameter width inconsistency
module wid_parameter_inconsistency_violation
  #(parameter WIDTH = 8)
  (input logic [WIDTH-1:0] data_in,
   output logic [7:0] data_out);  // WID_004: Hardcoded width instead of WIDTH
  
  assign data_out = data_in;
endmodule

// Better: Use parameter consistently
module good_parameter_usage
  #(parameter WIDTH = 8)
  (input logic [WIDTH-1:0] data_in,
   output logic [WIDTH-1:0] data_out);
  
  assign data_out = data_in;
endmodule

