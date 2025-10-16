// Copyright 2025 The Verible Authors.
// Edge case: Hierarchical path names (module hierarchy)

module edge_hierarchical_top (
  input wire clk,
  input wire rst_n
);

  logic subsystem_enable;
  logic subsystem_ready;
  
  edge_hierarchical_sub u_subsystem (
    .clk(clk),
    .rst_n(rst_n),
    .enable(subsystem_enable),
    .ready(subsystem_ready)
  );

endmodule

module edge_hierarchical_sub (
  input wire clk,
  input wire rst_n,
  input wire enable,
  output logic ready
);

  logic controller_state;
  logic datapath_active;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      controller_state <= 1'b0;
      datapath_active <= 1'b0;
      ready <= 1'b0;
    end
  end

endmodule

