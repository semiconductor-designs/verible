// Test case: Unused local variables
module unused_variables (
  input logic clk,
  input logic [7:0] data_in,
  output logic [7:0] data_out
);
  
  // WARNING: unused_var is declared but never used
  logic [7:0] unused_var;
  
  // OK: used_var is properly used
  logic [7:0] used_var;
  assign used_var = data_in;
  assign data_out = used_var;
  
  // Function with unused variable
  function automatic logic [7:0] process_data(logic [7:0] input_data);
    // WARNING: temp_unused is never used
    logic [7:0] temp_unused;
    
    // OK: temp_used is used
    logic [7:0] temp_used;
    temp_used = input_data & 8'hFF;
    return temp_used;
  endfunction
  
endmodule

