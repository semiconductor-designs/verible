// Copyright 2025 The Verible Authors.
// Edge case: Constraint blocks (for UVM randomization)

class transaction;
  rand bit [7:0] data;
  rand bit [3:0] addr;
  
  constraint valid_range {
    data inside {[0:100]};
    addr < 10;
  }
  
  constraint aligned {
    addr[0] == 0;  // Even addresses only
  }
endclass

module str_edge_constraint_block (
  input wire clk,
  input wire rst_n,
  input wire [7:0] data_in,
  input wire [3:0] addr_in,
  output logic [7:0] data_out
);

  logic [7:0] memory [15:0];
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_out <= 8'h00;
      for (int i = 0; i < 16; i++) memory[i] <= 8'h00;
    end else begin
      memory[addr_in] <= data_in;
      data_out <= memory[addr_in];
    end
  end

endmodule

