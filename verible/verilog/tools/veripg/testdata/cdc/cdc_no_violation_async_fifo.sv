// Copyright 2025 The Verible Authors.
// Negative test: Async FIFO with proper handshake - NO violations

module cdc_no_violation_async_fifo #(
  parameter DATA_WIDTH = 8,
  parameter DEPTH = 16
)(
  input wire wr_clk,
  input wire rd_clk,
  input wire rst_n,
  input wire [DATA_WIDTH-1:0] wr_data,
  input wire wr_en,
  output logic wr_full,
  output logic [DATA_WIDTH-1:0] rd_data,
  input wire rd_en,
  output logic rd_empty
);

  localparam ADDR_WIDTH = $clog2(DEPTH);
  
  // Dual-port RAM
  logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];
  
  // Gray-coded pointers
  logic [ADDR_WIDTH:0] wr_ptr_gray, wr_ptr_gray_next;
  logic [ADDR_WIDTH:0] rd_ptr_gray, rd_ptr_gray_next;
  
  // Binary pointers
  logic [ADDR_WIDTH:0] wr_ptr_bin, rd_ptr_bin;
  
  // Synchronized Gray pointers
  logic [ADDR_WIDTH:0] wr_ptr_gray_sync1, wr_ptr_gray_sync2;
  logic [ADDR_WIDTH:0] rd_ptr_gray_sync1, rd_ptr_gray_sync2;
  
  // Write domain
  always_ff @(posedge wr_clk or negedge rst_n) begin
    if (!rst_n) begin
      wr_ptr_bin <= '0;
      wr_ptr_gray <= '0;
    end else if (wr_en && !wr_full) begin
      wr_ptr_bin <= wr_ptr_bin + 1;
      wr_ptr_gray <= (wr_ptr_bin + 1) ^ ((wr_ptr_bin + 1) >> 1);
      mem[wr_ptr_bin[ADDR_WIDTH-1:0]] <= wr_data;
    end
  end
  
  // Read domain
  always_ff @(posedge rd_clk or negedge rst_n) begin
    if (!rst_n) begin
      rd_ptr_bin <= '0;
      rd_ptr_gray <= '0;
    end else if (rd_en && !rd_empty) begin
      rd_ptr_bin <= rd_ptr_bin + 1;
      rd_ptr_gray <= (rd_ptr_bin + 1) ^ ((rd_ptr_bin + 1) >> 1);
    end
  end
  
  assign rd_data = mem[rd_ptr_bin[ADDR_WIDTH-1:0]];
  
  // Synchronize write pointer to read domain
  always_ff @(posedge rd_clk or negedge rst_n) begin
    if (!rst_n) begin
      wr_ptr_gray_sync1 <= '0;
      wr_ptr_gray_sync2 <= '0;
    end else begin
      wr_ptr_gray_sync1 <= wr_ptr_gray;
      wr_ptr_gray_sync2 <= wr_ptr_gray_sync1;
    end
  end
  
  // Synchronize read pointer to write domain
  always_ff @(posedge wr_clk or negedge rst_n) begin
    if (!rst_n) begin
      rd_ptr_gray_sync1 <= '0;
      rd_ptr_gray_sync2 <= '0;
    end else begin
      rd_ptr_gray_sync1 <= rd_ptr_gray;
      rd_ptr_gray_sync2 <= rd_ptr_gray_sync1;
    end
  end
  
  // Full/Empty flags
  assign wr_full = (wr_ptr_gray == {~rd_ptr_gray_sync2[ADDR_WIDTH:ADDR_WIDTH-1], 
                                    rd_ptr_gray_sync2[ADDR_WIDTH-2:0]});
  assign rd_empty = (rd_ptr_gray == wr_ptr_gray_sync2);

endmodule

