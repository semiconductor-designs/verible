// Copyright 2025 The Verible Authors.
// Edge case: State backup/restore for power-down

module pwr_edge_backup_restore (
  input wire clk,
  input wire rst_n,
  input wire backup_trigger,
  input wire restore_trigger,
  input wire [31:0] working_data,
  output logic [31:0] restored_data
);

  // Working registers (lossy during power-down)
  logic [31:0] work_reg1;
  logic [31:0] work_reg2;
  
  // Backup registers (retention or always-on domain)
  logic [31:0] backup_reg1;
  logic [31:0] backup_reg2;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      work_reg1 <= 32'h0;
      work_reg2 <= 32'h0;
      backup_reg1 <= 32'h0;
      backup_reg2 <= 32'h0;
    end else if (backup_trigger) begin
      // Save state before power-down
      backup_reg1 <= work_reg1;
      backup_reg2 <= work_reg2;
    end else if (restore_trigger) begin
      // Restore state after power-up
      work_reg1 <= backup_reg1;
      work_reg2 <= backup_reg2;
    end else begin
      work_reg1 <= working_data;
      work_reg2 <= work_reg1;
    end
  end
  
  assign restored_data = work_reg2;

endmodule

