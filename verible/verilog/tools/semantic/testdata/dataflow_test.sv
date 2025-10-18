// Test file for data flow export
module dataflow_test;
  parameter WIDTH = 8;
  localparam DEPTH = 16;
  
  input wire clk;
  input wire [WIDTH-1:0] data_in;
  output reg [WIDTH-1:0] data_out;
  
  reg [WIDTH-1:0] buffer;
  wire [WIDTH-1:0] intermediate;
  
  assign intermediate = data_in & 8'hFF;
  
  always @(posedge clk) begin
    buffer <= intermediate;
    data_out <= buffer;
  end
endmodule

