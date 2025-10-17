// Test: Multiple parameters in one module

module fifo #(
  parameter DATA_WIDTH = 32,
  parameter DEPTH = 16,
  parameter ADDR_WIDTH = 4
) (
  input  logic                  clk,
  input  logic                  rst,
  input  logic                  wr_en,
  input  logic [DATA_WIDTH-1:0] wr_data,
  input  logic                  rd_en,
  output logic [DATA_WIDTH-1:0] rd_data,
  output logic                  full,
  output logic                  empty
);
  
  logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];
  logic [ADDR_WIDTH-1:0] wr_ptr, rd_ptr;
  logic [ADDR_WIDTH:0]   count;
  
  assign full = (count == DEPTH);
  assign empty = (count == 0);
  
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      wr_ptr <= 0;
      rd_ptr <= 0;
      count <= 0;
    end else begin
      if (wr_en && !full) begin
        mem[wr_ptr] <= wr_data;
        wr_ptr <= wr_ptr + 1;
        count <= count + 1;
      end
      if (rd_en && !empty) begin
        rd_data <= mem[rd_ptr];
        rd_ptr <= rd_ptr + 1;
        count <= count - 1;
      end
    end
  end
  
endmodule

module top;
  logic clk, rst, wr_en, rd_en;
  logic [31:0] wr_data, rd_data;
  logic full, empty;
  
  fifo dut (
    .clk(clk),
    .rst(rst),
    .wr_en(wr_en),
    .wr_data(wr_data),
    .rd_en(rd_en),
    .rd_data(rd_data),
    .full(full),
    .empty(empty)
  );
endmodule

