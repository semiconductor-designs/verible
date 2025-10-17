// VeriPG Hierarchical Design Pattern Test
// Tests validator on hierarchical VeriPG-style modules

module veripg_datapath #(
  parameter DATA_WIDTH = 32
)(
  input  wire                    clk,
  input  wire                    rst_n,
  input  wire [DATA_WIDTH-1:0]   data_in,
  input  wire                    valid_in,
  output wire [DATA_WIDTH-1:0]   data_out,
  output wire                    valid_out
);

  // Pipeline stages
  reg [DATA_WIDTH-1:0] stage1_data, stage2_data;
  reg                  stage1_valid, stage2_valid;

  // Stage 1
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      stage1_data  <= '0;
      stage1_valid <= 1'b0;
    end else begin
      stage1_data  <= data_in;
      stage1_valid <= valid_in;
    end
  end

  // Stage 2
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      stage2_data  <= '0;
      stage2_valid <= 1'b0;
    end else begin
      stage2_data  <= stage1_data;
      stage2_valid <= stage1_valid;
    end
  end

  assign data_out  = stage2_data;
  assign valid_out = stage2_valid;

endmodule

// Top-level integration
module veripg_top(
  input  wire        clk,
  input  wire        rst_n,
  input  wire [31:0] input_data,
  input  wire        input_valid,
  output wire [31:0] output_data,
  output wire        output_valid
);

  // Instantiate datapath
  veripg_datapath #(
    .DATA_WIDTH(32)
  ) u_datapath (
    .clk       (clk),
    .rst_n     (rst_n),
    .data_in   (input_data),
    .valid_in  (input_valid),
    .data_out  (output_data),
    .valid_out (output_valid)
  );

endmodule

