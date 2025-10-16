// Test case for STR_007: Generate block without label
module str_unlabeled_generate_violation;
  parameter N = 4;
  logic [N-1:0] data;
  
  // STR_007: Generate block without label
  generate
    for (genvar i = 0; i < N; i++) begin  // Missing label!
      assign data[i] = 1'b0;
    end
  endgenerate
  
  // Good: labeled generate block
  generate
    for (genvar j = 0; j < N; j++) begin : gen_loop
      // label present
    end
  endgenerate
endmodule

