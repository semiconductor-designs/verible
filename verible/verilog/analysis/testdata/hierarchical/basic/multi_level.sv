// Multi-level module hierarchy test
// Purpose: Test deep hierarchies (3+ levels)

module level3_module (
  input  logic data_in,
  output logic data_out
);
  assign data_out = ~data_in;
endmodule

module level2_module (
  input  logic data_in,
  output logic data_out
);
  logic intermediate;
  
  level3_module l3_inst (
    .data_in(data_in),
    .data_out(intermediate)
  );
  
  assign data_out = intermediate;
endmodule

module level1_module (
  input  logic data_in,
  output logic data_out
);
  logic intermediate;
  
  level2_module l2_inst (
    .data_in(data_in),
    .data_out(intermediate)
  );
  
  assign data_out = intermediate;
endmodule

module top_module (
  input  logic clk,
  input  logic data,
  output logic result
);
  logic level1_out;
  
  level1_module l1_inst (
    .data_in(data),
    .data_out(level1_out)
  );
  
  assign result = level1_out;
endmodule

