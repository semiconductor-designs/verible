// Test case for STR_002: Module exceeds complexity threshold (50+ statements)
module str_complexity_violation (
  input logic clk,
  input logic rst_n,
  output logic [7:0] result
);
  // STR_002: Too many statements (simplified for testing)
  logic [7:0] a, b, c, d, e, f, g, h;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      a <= 0; b <= 0; c <= 0; d <= 0;
      e <= 0; f <= 0; g <= 0; h <= 0;
      result <= 0;
    end else begin
      a <= a + 1;
      b <= a + b;
      c <= b + c;
      d <= c + d;
      e <= d + e;
      f <= e + f;
      g <= f + g;
      h <= g + h;
      result <= h;
      // ... imagine 40+ more statements here
    end
  end
  // Module has high cyclomatic complexity
endmodule

