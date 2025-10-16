// Test file for STR_007: Generate block without label

module str_unlabeled_generate #(
  parameter WIDTH = 8
)(
  input wire clk,
  input wire [WIDTH-1:0] data_in,
  output logic [WIDTH-1:0] data_out
);
  // Violation: Generate block without label
  generate
    for (genvar i = 0; i < WIDTH; i++) begin  // Should have label after begin
      always_ff @(posedge clk) begin
        data_out[i] <= data_in[i];
      end
    end
  endgenerate
  
  // Correct way:
  // generate
  //   for (genvar i = 0; i < WIDTH; i++) begin : gen_bits
  //     always_ff @(posedge clk) begin
  //       data_out[i] <= data_in[i];
  //     end
  //   end
  // endgenerate
endmodule

