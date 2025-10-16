// Copyright 2025 The Verible Authors.
// Edge case: Package and import names

package system_config_pkg;
  parameter int SYSTEM_DATA_WIDTH = 32;
  parameter int SYSTEM_ADDR_WIDTH = 16;
  parameter int MAX_BURST_LENGTH = 256;
  
  typedef struct packed {
    logic [31:0] config_register;
    logic [31:0] status_register;
    logic enable_flag;
  } system_registers_t;
endpackage

module edge_package_names 
  import system_config_pkg::*;
(
  input wire clk,
  input wire rst_n,
  input wire [SYSTEM_DATA_WIDTH-1:0] data_in,
  output logic [SYSTEM_DATA_WIDTH-1:0] data_out
);

  system_registers_t system_regs;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      system_regs <= '0;
      data_out <= '0;
    end
  end

endmodule

