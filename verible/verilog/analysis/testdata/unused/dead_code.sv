// Test case: Dead code (unreachable code paths)
module dead_code (
  input logic sel,
  input logic data,
  output logic result
);
  
  localparam ALWAYS_TRUE = 1'b1;
  localparam ALWAYS_FALSE = 1'b0;
  
  logic temp;
  
  always_comb begin
    // WARNING: else branch is dead code (condition is always true)
    if (ALWAYS_TRUE) begin
      temp = data;
    end else begin
      temp = ~data;  // DEAD CODE - never executed
    end
  end
  
  logic temp2;
  always_comb begin
    // WARNING: if branch is dead code (condition is always false)
    if (ALWAYS_FALSE) begin
      temp2 = data;  // DEAD CODE - never executed
    end else begin
      temp2 = ~data;
    end
  end
  
  // OK: This is reachable code with runtime condition
  logic temp3;
  always_comb begin
    if (sel) begin
      temp3 = data;  // Reachable
    end else begin
      temp3 = ~data;  // Also reachable
    end
  end
  
  assign result = temp & temp2 & temp3;
  
endmodule

