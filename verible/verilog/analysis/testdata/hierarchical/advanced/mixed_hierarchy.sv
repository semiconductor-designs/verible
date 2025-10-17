// Mixed hierarchy test
// Purpose: Test combination of modules, classes, and interfaces

interface data_bus_if (input logic clk);
  logic [31:0] addr;
  logic [31:0] data;
  logic        valid;
  logic        ready;
  
  modport master (
    output addr,
    output data,
    output valid,
    input  ready
  );
  
  modport slave (
    input  addr,
    input  data,
    input  valid,
    output ready
  );
endinterface

class Transaction;
  logic [31:0] address;
  logic [31:0] data;
  
  function new(logic [31:0] addr, logic [31:0] d);
    address = addr;
    data = d;
  endfunction
  
  virtual function void display();
    $display("Transaction: addr=0x%0h, data=0x%0h", address, data);
  endfunction
endclass

class WriteTransaction extends Transaction;
  function new(logic [31:0] addr, logic [31:0] d);
    super.new(addr, d);
  endfunction
  
  virtual function void display();
    $display("Write: addr=0x%0h, data=0x%0h", address, data);
  endfunction
endclass

module bus_master (
  input logic clk,
  input logic reset,
  data_bus_if.master bus
);
  WriteTransaction trans_queue[$];
  
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      bus.valid <= 1'b0;
    end else if (trans_queue.size() > 0 && bus.ready) begin
      WriteTransaction trans = trans_queue.pop_front();
      bus.addr  <= trans.address;
      bus.data  <= trans.data;
      bus.valid <= 1'b1;
      trans.display();
    end else begin
      bus.valid <= 1'b0;
    end
  end
endmodule

module bus_slave (
  input logic clk,
  input logic reset,
  data_bus_if.slave bus
);
  logic [31:0] memory[256];
  
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      bus.ready <= 1'b1;
    end else if (bus.valid && bus.ready) begin
      memory[bus.addr[7:0]] <= bus.data;
      $display("Slave: Wrote 0x%0h to addr 0x%0h", bus.data, bus.addr);
    end
  end
endmodule

module bus_system (
  input logic clk,
  input logic reset
);
  data_bus_if bus_inst(.clk(clk));
  
  bus_master master (
    .clk(clk),
    .reset(reset),
    .bus(bus_inst.master)
  );
  
  bus_slave slave (
    .clk(clk),
    .reset(reset),
    .bus(bus_inst.slave)
  );
endmodule

