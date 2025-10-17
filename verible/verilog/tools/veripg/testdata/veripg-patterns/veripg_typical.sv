// VeriPG Typical Pattern Test
// This file mimics typical VeriPG-generated code patterns

module veripg_counter #(
  parameter WIDTH = 8
)(
  input  wire              clk,
  input  wire              rst_n,
  input  wire              enable,
  input  wire [WIDTH-1:0]  load_value,
  output reg  [WIDTH-1:0]  count
);

  // Typical VeriPG always_ff block
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      count <= '0;
    end else begin
      if (enable) begin
        count <= count + 1'b1;
      end
    end
  end

endmodule

// VeriPG typical FSM pattern
module veripg_fsm(
  input  wire clk,
  input  wire rst_n,
  input  wire start,
  output reg  busy,
  output reg  done
);

  typedef enum logic [1:0] {
    IDLE  = 2'b00,
    BUSY  = 2'b01,
    DONE  = 2'b10
  } state_t;

  state_t state, next_state;

  // State register
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state <= IDLE;
    end else begin
      state <= next_state;
    end
  end

  // Next state logic
  always_comb begin
    next_state = state;
    busy = 1'b0;
    done = 1'b0;

    case (state)
      IDLE: begin
        if (start) next_state = BUSY;
      end
      BUSY: begin
        busy = 1'b1;
        next_state = DONE;
      end
      DONE: begin
        done = 1'b1;
        next_state = IDLE;
      end
    endcase
  end

endmodule

