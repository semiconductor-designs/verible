// Simple module hierarchy test
// Purpose: Test basic parent-child module relationships

module child_module (
  input  logic clk,
  input  logic reset,
  output logic out
);
  always_ff @(posedge clk) begin
    if (reset)
      out <= 1'b0;
    else
      out <= 1'b1;
  end
endmodule

module parent_module (
  input  logic clk,
  input  logic reset,
  output logic result
);
  logic child_out;
  
  child_module child_inst (
    .clk(clk),
    .reset(reset),
    .out(child_out)
  );
  
  assign result = child_out;
endmodule

