// Enum type hierarchy test
// Purpose: Test enum compatibility across modules

typedef enum logic [1:0] {
  IDLE   = 2'b00,
  ACTIVE = 2'b01,
  WAIT   = 2'b10,
  ERROR  = 2'b11
} state_t;

typedef enum logic [2:0] {
  CMD_NOP   = 3'b000,
  CMD_READ  = 3'b001,
  CMD_WRITE = 3'b010,
  CMD_RESET = 3'b011
} command_t;

module state_controller (
  input  logic    clk,
  input  logic    reset,
  input  command_t cmd_in,
  output state_t   state_out
);
  state_t current_state;
  
  always_ff @(posedge clk or posedge reset) begin
    if (reset)
      current_state <= IDLE;
    else begin
      case (cmd_in)
        CMD_READ, CMD_WRITE: current_state <= ACTIVE;
        CMD_RESET:           current_state <= IDLE;
        default:             current_state <= WAIT;
      endcase
    end
  end
  
  assign state_out = current_state;
endmodule

module command_decoder (
  input  logic     clk,
  input  logic [2:0] cmd_bits,
  output command_t cmd_out
);
  always_ff @(posedge clk) begin
    cmd_out <= command_t'(cmd_bits);
  end
endmodule

module controller_system (
  input  logic    clk,
  input  logic    reset,
  input  logic [2:0] cmd_bits,
  output state_t  state
);
  command_t decoded_cmd;
  
  command_decoder decoder (
    .clk(clk),
    .cmd_bits(cmd_bits),
    .cmd_out(decoded_cmd)
  );
  
  state_controller ctrl (
    .clk(clk),
    .reset(reset),
    .cmd_in(decoded_cmd),
    .state_out(state)
  );
endmodule

