// Copyright 2025 The Verible Authors.
// Edge case: Module with interface ports

interface simple_bus;
  logic [7:0] data;
  logic valid;
  logic ready;
endinterface

module str_edge_interface_ports (
  input wire clk,
  input wire rst_n,
  simple_bus.master bus_out,
  simple_bus.slave bus_in
);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      bus_out.data <= 8'h00;
      bus_out.valid <= 1'b0;
      bus_in.ready <= 1'b0;
    end else begin
      bus_out.data <= bus_in.data;
      bus_out.valid <= bus_in.valid;
      bus_in.ready <= bus_out.ready;
    end
  end

endmodule

