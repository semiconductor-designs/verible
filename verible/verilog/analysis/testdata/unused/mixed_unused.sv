// Test case: Complex real-world scenario with various unused entities
module mixed_unused (
  input logic clk,
  input logic rst_n,
  input logic [7:0] data_in,
  input logic unused_input,        // OK: Input (filtered)
  output logic [7:0] data_out,
  output logic unused_output       // OK: Output (filtered)
);
  
  // WARNING: Completely unused signal
  logic completely_unused;
  
  // WARNING: Write-only signal
  logic write_only;
  always_ff @(posedge clk) begin
    write_only <= data_in[0];
  end
  
  // WARNING: Read-only signal (undriven)
  logic read_only;
  logic consumer;
  assign consumer = read_only;
  
  // OK: Properly used signal
  logic [7:0] properly_used;
  assign properly_used = data_in;
  assign data_out = properly_used;
  
  // WARNING: Unused function
  function automatic logic [7:0] unused_func(logic [7:0] x);
    return x + 8'h01;
  endfunction
  
  // OK: Called function
  function automatic logic [7:0] called_func(logic [7:0] x);
    return x & 8'hFF;
  endfunction
  
  logic [7:0] temp;
  assign temp = called_func(data_in);
  
  // WARNING: Unused variable
  logic [7:0] unused_var;
  
  // OK: Used variable
  logic [7:0] used_var;
  assign used_var = temp;
  
  // OK: Intentionally unused (filtered by pattern)
  logic unused_for_future;
  
endmodule

// WARNING: Unused module (never instantiated)
module helper_module (
  input logic a,
  output logic b
);
  assign b = ~a;
endmodule

