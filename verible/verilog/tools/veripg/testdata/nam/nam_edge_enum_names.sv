// Copyright 2025 The Verible Authors.
// Edge case: Enum value naming

module edge_enum_names (
  input wire clk,
  input wire rst_n,
  input wire [1:0] command,
  output logic [7:0] result
);

  typedef enum logic [1:0] {
    STATE_IDLE = 2'b00,
    STATE_ACTIVE = 2'b01,
    STATE_WAIT = 2'b10,
    STATE_ERROR = 2'b11
  } state_t;
  
  typedef enum logic [2:0] {
    CMD_NOP = 3'b000,
    CMD_READ = 3'b001,
    CMD_WRITE = 3'b010,
    CMD_RESET = 3'b011,
    CMD_FLUSH = 3'b100
  } command_t;
  
  state_t current_state;
  state_t next_state;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      current_state <= STATE_IDLE;
    else
      current_state <= next_state;
  end

endmodule

