// Test: Using default parameter values without override

module configurable #(
  parameter ENABLE_FEATURE_A = 1,
  parameter ENABLE_FEATURE_B = 0,
  parameter TIMEOUT = 1000,
  parameter MODE = "FAST"
) (
  input  logic clk,
  input  logic start,
  output logic done
);
  
  generate
    if (ENABLE_FEATURE_A) begin : gen_feature_a
      // Feature A logic
      always_ff @(posedge clk) begin
        if (start)
          $display("Feature A enabled, MODE=%s", MODE);
      end
    end
    
    if (ENABLE_FEATURE_B) begin : gen_feature_b
      // Feature B logic
      always_ff @(posedge clk) begin
        if (start)
          $display("Feature B enabled");
      end
    end
  endgenerate
  
  // Use TIMEOUT parameter
  localparam COUNTER_MAX = TIMEOUT;
  
  assign done = 1'b0;
  
endmodule

module top;
  logic clk, start, done;
  
  // Use all default parameters - no overrides
  configurable default_config (
    .clk(clk),
    .start(start),
    .done(done)
  );
  
  // Override some parameters
  configurable custom_config (
    .ENABLE_FEATURE_A(0),
    .ENABLE_FEATURE_B(1),
    .TIMEOUT(2000),
    .MODE("SLOW")
  ) custom (
    .clk(clk),
    .start(start),
    .done(done)
  );
endmodule

