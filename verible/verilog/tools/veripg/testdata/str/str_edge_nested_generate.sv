// Copyright 2025 The Verible Authors.
// Edge case: Nested generate blocks

module str_edge_nested_generate #(
  parameter int ROWS = 4,
  parameter int COLS = 4
) (
  input wire clk,
  input wire rst_n,
  input wire [ROWS*COLS-1:0] data_in,
  output logic [ROWS*COLS-1:0] data_out
);

  logic [ROWS-1:0][COLS-1:0] array;
  
  genvar row, col;
  generate
    for (row = 0; row < ROWS; row++) begin : gen_rows
      for (col = 0; col < COLS; col++) begin : gen_cols
        always_ff @(posedge clk or negedge rst_n) begin
          if (!rst_n)
            array[row][col] <= 1'b0;
          else
            array[row][col] <= data_in[row*COLS + col];
        end
        
        assign data_out[row*COLS + col] = array[row][col];
      end
    end
  endgenerate

endmodule

