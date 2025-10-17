// VeriPG Interface-Based Design Pattern Test
// Tests validator on interface-heavy VeriPG patterns

// AXI-Lite style interface
interface veripg_axil_if #(
  parameter ADDR_WIDTH = 32,
  parameter DATA_WIDTH = 32
);
  logic                    aclk;
  logic                    aresetn;
  logic [ADDR_WIDTH-1:0]   awaddr;
  logic                    awvalid;
  logic                    awready;
  logic [DATA_WIDTH-1:0]   wdata;
  logic                    wvalid;
  logic                    wready;
  logic [1:0]              bresp;
  logic                    bvalid;
  logic                    bready;
  logic [ADDR_WIDTH-1:0]   araddr;
  logic                    arvalid;
  logic                    arready;
  logic [DATA_WIDTH-1:0]   rdata;
  logic [1:0]              rresp;
  logic                    rvalid;
  logic                    rready;

  modport master (
    input  aclk, aresetn, awready, wready, bresp, bvalid, arready, rdata, rresp, rvalid,
    output awaddr, awvalid, wdata, wvalid, bready, araddr, arvalid, rready
  );

  modport slave (
    input  aclk, aresetn, awaddr, awvalid, wdata, wvalid, bready, araddr, arvalid, rready,
    output awready, wready, bresp, bvalid, arready, rdata, rresp, rvalid
  );

endinterface

// Module using interface
module veripg_axil_reg #(
  parameter ADDR_WIDTH = 32,
  parameter DATA_WIDTH = 32
)(
  veripg_axil_if.slave axi
);

  // Register array
  logic [DATA_WIDTH-1:0] registers [0:15];

  // Write logic
  always_ff @(posedge axi.aclk or negedge axi.aresetn) begin
    if (!axi.aresetn) begin
      axi.awready <= 1'b0;
      axi.wready  <= 1'b0;
      axi.bvalid  <= 1'b0;
      axi.bresp   <= 2'b00;
      for (int i = 0; i < 16; i++) begin
        registers[i] <= '0;
      end
    end else begin
      // Write transaction
      if (axi.awvalid && axi.wvalid && !axi.bvalid) begin
        registers[axi.awaddr[5:2]] <= axi.wdata;
        axi.awready <= 1'b1;
        axi.wready  <= 1'b1;
        axi.bvalid  <= 1'b1;
        axi.bresp   <= 2'b00;  // OKAY
      end else if (axi.bready && axi.bvalid) begin
        axi.bvalid  <= 1'b0;
        axi.awready <= 1'b0;
        axi.wready  <= 1'b0;
      end
    end
  end

  // Read logic
  always_ff @(posedge axi.aclk or negedge axi.aresetn) begin
    if (!axi.aresetn) begin
      axi.arready <= 1'b0;
      axi.rvalid  <= 1'b0;
      axi.rdata   <= '0;
      axi.rresp   <= 2'b00;
    end else begin
      // Read transaction
      if (axi.arvalid && !axi.rvalid) begin
        axi.rdata   <= registers[axi.araddr[5:2]];
        axi.arready <= 1'b1;
        axi.rvalid  <= 1'b1;
        axi.rresp   <= 2'b00;  // OKAY
      end else if (axi.rready && axi.rvalid) begin
        axi.rvalid  <= 1'b0;
        axi.arready <= 1'b0;
      end
    end
  end

endmodule

