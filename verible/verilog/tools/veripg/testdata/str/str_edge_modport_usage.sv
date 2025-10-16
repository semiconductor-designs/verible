// Copyright 2025 The Verible Authors.
// Edge case: Interface with modports

interface bus_if;
  logic [7:0] data;
  logic valid;
  logic ready;
  
  modport master (
    output data,
    output valid,
    input ready
  );
  
  modport slave (
    input data,
    input valid,
    output ready
  );
endinterface

module master_module (
  input wire clk,
  input wire rst_n,
  bus_if.master bus
);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      bus.data <= 8'h00;
      bus.valid <= 1'b0;
    end else begin
      bus.data <= 8'hAA;
      bus.valid <= 1'b1;
    end
  end
endmodule

module slave_module (
  input wire clk,
  input wire rst_n,
  bus_if.slave bus
);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      bus.ready <= 1'b0;
    end else begin
      bus.ready <= bus.valid;
    end
  end
endmodule

module str_edge_modport_usage (
  input wire clk,
  input wire rst_n
);

  bus_if bus_instance();
  
  master_module u_master (
    .clk(clk),
    .rst_n(rst_n),
    .bus(bus_instance)
  );
  
  slave_module u_slave (
    .clk(clk),
    .rst_n(rst_n),
    .bus(bus_instance)
  );

endmodule

