// Test case: Write-only signals (never read)
module write_only_signals (
  input logic clk,
  input logic data_in
);
  
  // WARNING: write_only is written but never read
  logic write_only;
  always_ff @(posedge clk) begin
    write_only <= data_in;
  end
  // No reader for write_only - this is suspicious
  
  // WARNING: assigned_but_not_read has assignment but no readers
  logic assigned_but_not_read;
  assign assigned_but_not_read = data_in & 1'b1;
  // No reader - likely a bug
  
  // OK: properly_used is both written and read
  logic properly_used;
  assign properly_used = data_in;
  
  logic output_reg;
  assign output_reg = properly_used;
  
endmodule

