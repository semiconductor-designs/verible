// Copyright 2025 The Verible Authors.
// Edge case: Interface signal names

interface axi_lite_if #(
  parameter int ADDR_WIDTH = 32,
  parameter int DATA_WIDTH = 32
);
  logic [ADDR_WIDTH-1:0] awaddr;
  logic awvalid;
  logic awready;
  logic [DATA_WIDTH-1:0] wdata;
  logic [DATA_WIDTH/8-1:0] wstrb;
  logic wvalid;
  logic wready;
  logic [1:0] bresp;
  logic bvalid;
  logic bready;
  
  modport master (
    output awaddr, awvalid, wdata, wstrb, wvalid, bready,
    input awready, wready, bresp, bvalid
  );
  
  modport slave (
    input awaddr, awvalid, wdata, wstrb, wvalid, bready,
    output awready, wready, bresp, bvalid
  );
endinterface

module edge_interface_names (
  input wire clk,
  input wire rst_n,
  axi_lite_if.master axi_bus
);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      axi_bus.awvalid <= 1'b0;
      axi_bus.wvalid <= 1'b0;
    end
  end

endmodule

