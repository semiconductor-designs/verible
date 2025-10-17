// Non-blocking assignments in sequential logic
module nonblocking_assignment (
  input  logic clk,
  input  logic rst_n,
  input  logic d,
  output logic q,
  output logic q_delayed
);
  
  // Sequential logic with non-blocking assignments
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      q <= 1'b0;
      q_delayed <= 1'b0;
    end else begin
      q <= d;           // q driven by d
      q_delayed <= q;   // q_delayed driven by q
    end
  end
  
endmodule

