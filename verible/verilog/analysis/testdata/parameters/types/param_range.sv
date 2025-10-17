// Test: Parameters used in bit ranges

module memory #(
  parameter ADDR_WIDTH = 8,
  parameter DATA_WIDTH = 32,
  parameter DEPTH = 256
) (
  input  logic                    clk,
  input  logic                    wr_en,
  input  logic [ADDR_WIDTH-1:0]   addr,
  input  logic [DATA_WIDTH-1:0]   wr_data,
  output logic [DATA_WIDTH-1:0]   rd_data
);
  
  // Use parameters in array declaration
  logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];
  
  always_ff @(posedge clk) begin
    if (wr_en)
      mem[addr] <= wr_data;
    rd_data <= mem[addr];
  end
  
endmodule

module top;
  logic clk, wr_en;
  logic [9:0]  addr;
  logic [63:0] wr_data, rd_data;
  
  // Override to larger memory
  memory #(
    .ADDR_WIDTH(10),
    .DATA_WIDTH(64),
    .DEPTH(1024)
  ) mem_inst (
    .clk(clk),
    .wr_en(wr_en),
    .addr(addr),
    .wr_data(wr_data),
    .rd_data(rd_data)
  );
endmodule

