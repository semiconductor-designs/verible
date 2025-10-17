// Mutually exclusive conditional drivers (legal)
module conditional_drivers (
  input  logic sel,
  input  logic a,
  input  logic b,
  output logic result
);
  
  logic internal;
  
  // OK: Multiple drivers but mutually exclusive
  always_comb begin
    if (sel)
      internal = a;
    else
      internal = b;
  end
  
  assign result = internal;
  
endmodule

