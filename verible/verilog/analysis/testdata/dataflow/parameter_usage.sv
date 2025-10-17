// Parameter usage in data flow
module parameter_usage #(
  parameter WIDTH = 8,
  parameter INIT_VALUE = 8'h00
) (
  input  logic [WIDTH-1:0] data_in,
  output logic [WIDTH-1:0] data_out
);
  
  // Parameters affect data flow but are constants
  logic [WIDTH-1:0] register;
  
  always_comb begin
    register = data_in | INIT_VALUE;
  end
  
  assign data_out = register;
  
endmodule

