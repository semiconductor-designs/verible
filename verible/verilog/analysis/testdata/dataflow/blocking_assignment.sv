// Blocking assignments in combinational logic
module blocking_assignment (
  input  logic a,
  input  logic b,
  output logic c,
  output logic d
);
  
  // Combinational always block with blocking assignments
  always_comb begin
    c = a & b;    // c driven by a and b
    d = c | a;    // d driven by c and a
  end
  
endmodule

