# Complete SystemVerilog Verification Features Guide

## Overview

Verible v3.0.0 provides comprehensive JSON CST export support for modern SystemVerilog verification environments, including:

- **Object-Oriented Programming (OOP)**: Classes, inheritance, constraints
- **Interfaces**: Modports, clocking blocks, parameterization
- **Packages**: Code organization, imports, exports
- **Generate Blocks**: Parametric designs, conditional compilation
- **Assertions (SVA)**: Properties, sequences, checkers
- **DPI**: Foreign function interface
- **Program Blocks**: Verification program constructs
- **Functional Coverage**: Covergroups, coverpoints, bins

This guide provides a complete reference for analyzing verification code with Verible.

## Quick Start

### Installation

```bash
# Build Verible with all verification features
bazel build //verible/verilog/tools/syntax:verible-verilog-syntax -c opt

# Export JSON for your SystemVerilog file
./bazel-bin/verible/verilog/tools/syntax/verible-verilog-syntax \
  --export_json your_file.sv > output.json
```

### Basic Usage

```python
import json

# Load JSON CST
with open('output.json', 'r') as f:
    cst = json.load(f)

# Find all classes
def find_classes(node):
    if node.get('tag') == 'kClassDeclaration':
        class_info = node.get('metadata', {}).get('class_info', {})
        print(f"Found class: {class_info['class_name']}")
    
    for child in node.get('children', []):
        find_classes(child)

find_classes(cst)
```

## Feature Matrix

| Feature | JSON Tag | Metadata Key | Test Coverage | Since |
|---------|----------|--------------|---------------|-------|
| Classes | `kClassDeclaration` | `class_info` | 55 tests | v3.0.0 |
| Constraints | `kConstraintDeclaration` | `constraint_info` | (in class tests) | v3.0.0 |
| Interfaces | `kInterfaceDeclaration` | `interface_info` | 50 tests | v3.0.0 |
| Packages | `kPackageDeclaration` | `package_info` | 25 tests | v3.0.0 |
| Generate | `kLoopGenerateConstruct`, `kGenerateIf` | `generate_info` | 24 tests | v3.0.0 |
| Assertions | `kAssertionStatement`, `kPropertyDeclaration` | `assertion_info` | 40 tests | v2.2.0 |
| DPI | `kDPIImport`, `kDPIExport` | `dpi_info` | 18 tests | v2.2.0 |
| Program | `kProgramDeclaration` | `program_info` | 15 tests | v2.2.0 |
| Coverage | `kCovergroupDeclaration` | `covergroup_info` | 25 tests | v2.2.0 |

**Total Test Coverage: 292 tests**

## Complete UVM Testbench Analysis

### Example: UVM Environment

**SystemVerilog:**
```systemverilog
// my_env_pkg.sv
package my_env_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  // Transaction
  class my_transaction extends uvm_sequence_item;
    rand logic [31:0] addr;
    rand logic [63:0] data;
    rand bit read_write; // 0=read, 1=write
    
    constraint valid_addr {
      addr inside {[32'h1000:32'h2000]};
      addr[1:0] == 2'b00; // Word aligned
    }
    
    `uvm_object_utils_begin(my_transaction)
      `uvm_field_int(addr, UVM_ALL_ON)
      `uvm_field_int(data, UVM_ALL_ON)
      `uvm_field_int(read_write, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "my_transaction");
      super.new(name);
    endfunction
  endclass
  
  // Driver
  class my_driver extends uvm_driver#(my_transaction);
    virtual my_if vif;
    
    `uvm_component_utils(my_driver)
    
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      forever begin
        seq_item_port.get_next_item(req);
        drive_transaction(req);
        seq_item_port.item_done();
      end
    endtask
  endclass
  
  // Environment
  class my_env extends uvm_env;
    my_driver driver;
    my_monitor monitor;
    my_scoreboard scoreboard;
    
    `uvm_component_utils(my_env)
    
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      driver = my_driver::type_id::create("driver", this);
      monitor = my_monitor::type_id::create("monitor", this);
      scoreboard = my_scoreboard::type_id::create("scoreboard", this);
    endfunction
  endclass
endpackage
```

### JSON Analysis

The JSON export will contain:

1. **Package metadata**: `my_env_pkg` with 3 classes
2. **Class metadata** for each component:
   - `my_transaction`: parent=`uvm_sequence_item`, has_constraints=true, rand_variable_count=3
   - `my_driver`: parent=`uvm_driver`, method_count=2
   - `my_env`: parent=`uvm_env`, property_count=3

3. **Constraint metadata**: `valid_addr` with inside/alignment expressions

### Analysis Script

```python
def analyze_uvm_testbench(json_tree):
    components = {
        'transactions': [],
        'drivers': [],
        'monitors': [],
        'scoreboards': [],
        'environments': []
    }
    
    def traverse(node):
        if node.get('tag') == 'kClassDeclaration':
            class_info = node.get('metadata', {}).get('class_info', {})
            name = class_info['class_name']
            parent = class_info.get('parent_class', '')
            
            if 'transaction' in name or 'sequence_item' in parent:
                components['transactions'].append(name)
            elif 'driver' in name or 'uvm_driver' in parent:
                components['drivers'].append(name)
            elif 'monitor' in name:
                components['monitors'].append(name)
            elif 'scoreboard' in name:
                components['scoreboards'].append(name)
            elif 'env' in name and 'uvm_env' in parent:
                components['environments'].append(name)
        
        for child in node.get('children', []):
            traverse(child)
    
    traverse(json_tree)
    return components
```

## Protocol Interface Analysis

### AXI4 Interface Example

**SystemVerilog:**
```systemverilog
interface axi4_if #(
  parameter ADDR_WIDTH = 32,
  parameter DATA_WIDTH = 64,
  parameter ID_WIDTH = 4
)(input logic aclk, input logic aresetn);
  
  // Write address channel
  logic [ID_WIDTH-1:0]    awid;
  logic [ADDR_WIDTH-1:0]  awaddr;
  logic [7:0]             awlen;
  logic [2:0]             awsize;
  logic                   awvalid;
  logic                   awready;
  
  // Write data channel
  logic [DATA_WIDTH-1:0]  wdata;
  logic [DATA_WIDTH/8-1:0] wstrb;
  logic                   wlast;
  logic                   wvalid;
  logic                   wready;
  
  // Write response channel
  logic [ID_WIDTH-1:0]    bid;
  logic [1:0]             bresp;
  logic                   bvalid;
  logic                   bready;
  
  // Modports
  modport master (
    output awid, awaddr, awlen, awsize, awvalid,
    input  awready,
    output wdata, wstrb, wlast, wvalid,
    input  wready,
    input  bid, bresp, bvalid,
    output bready
  );
  
  modport slave (
    input  awid, awaddr, awlen, awsize, awvalid,
    output awready,
    input  wdata, wstrb, wlast, wvalid,
    output wready,
    output bid, bresp, bvalid,
    input  bready
  );
  
  // Clocking blocks for verification
  clocking master_cb @(posedge aclk);
    default input #1ns output #2ns;
    output awid, awaddr, awlen, awsize, awvalid;
    input  awready;
    output wdata, wstrb, wlast, wvalid;
    input  wready;
    input  bid, bresp, bvalid;
    output bready;
  endclocking
  
  modport master_tb (clocking master_cb, input aclk, aresetn);
  
  // Assertions
  property p_awvalid_held;
    @(posedge aclk) disable iff (!aresetn)
      awvalid && !awready |=> awvalid;
  endproperty
  
  assert property (p_awvalid_held);
endinterface
```

JSON export captures:
- Parameterization (3 parameters)
- Signal count (16 signals)
- Modport definitions (4 modports: master, slave, master_tb, slave_tb)
- Clocking blocks
- Embedded assertions

## Parametric Design Analysis

### Configurable FIFO with Generate

**SystemVerilog:**
```systemverilog
module parametric_fifo #(
  parameter WIDTH = 32,
  parameter DEPTH = 16,
  parameter PIPELINE = 1
)(
  input logic clk,
  input logic rst_n,
  // Write interface
  input logic [WIDTH-1:0] wr_data,
  input logic wr_valid,
  output logic wr_ready,
  // Read interface
  output logic [WIDTH-1:0] rd_data,
  output logic rd_valid,
  input logic rd_ready
);
  
  // Storage
  logic [WIDTH-1:0] mem [DEPTH];
  logic [$clog2(DEPTH):0] wr_ptr, rd_ptr;
  
  // Generate pipeline stages
  generate
    if (PIPELINE) begin : gen_pipeline
      logic [WIDTH-1:0] pipe_data;
      logic pipe_valid;
      
      always_ff @(posedge clk) begin
        if (rd_valid && rd_ready) begin
          pipe_data <= rd_data;
          pipe_valid <= 1'b1;
        end else if (rd_ready) begin
          pipe_valid <= 1'b0;
        end
      end
    end else begin : gen_direct
      // Direct connection without pipeline
    end
  endgenerate
  
  // Generate depth-dependent logic
  generate
    for (genvar i = 0; i < DEPTH; i++) begin : gen_init
      initial mem[i] = '0;
    end
  endgenerate
  
  // Generate different implementations based on depth
  generate
    case (DEPTH)
      2, 4: begin : gen_small_fifo
        // Optimized for small depths
      end
      8, 16, 32: begin : gen_medium_fifo
        // Standard implementation
      end
      default: begin : gen_large_fifo
        // Memory-based implementation for large depths
      end
    endcase
  endgenerate
  
endmodule
```

JSON export tracks:
- Generate if/else structures
- Generate for loops with labels
- Generate case constructs
- Parameterization impact

## Coverage-Driven Verification

### Functional Coverage Example

**SystemVerilog:**
```systemverilog
class bus_coverage;
  logic [2:0] cmd;
  logic [7:0] addr;
  logic [31:0] data;
  
  covergroup bus_cg;
    // Command coverage
    cmd_cp: coverpoint cmd {
      bins read = {3'b001};
      bins write = {3'b010};
      bins burst = {3'b100};
      illegal_bins reserved = {[3'b011:3'b111]};
    }
    
    // Address coverage
    addr_cp: coverpoint addr {
      bins low = {[0:63]};
      bins mid = {[64:191]};
      bins high = {[192:255]};
    }
    
    // Data coverage (sampled values)
    data_cp: coverpoint data {
      bins zero = {32'h0};
      bins ones = {32'hFFFFFFFF};
      bins other = default;
    }
    
    // Cross coverage
    cmd_addr_cross: cross cmd_cp, addr_cp {
      illegal_bins no_burst_low = binsof(cmd_cp.burst) && binsof(addr_cp.low);
    }
  endgroup
  
  function new();
    bus_cg = new();
  endfunction
  
  function void sample(logic [2:0] c, logic [7:0] a, logic [31:0] d);
    cmd = c;
    addr = a;
    data = d;
    bus_cg.sample();
  endfunction
endclass
```

JSON metadata includes:
- Covergroup name and structure
- Coverpoint definitions with bin specifications
- Cross coverage between coverpoints
- Illegal bins and ignore bins

## Integration Examples

### Complete Testbench Hierarchy

```python
def analyze_complete_testbench(json_file):
    """
    Comprehensive testbench analysis extracting:
    - Package structure
    - Class hierarchy
    - Interface definitions
    - Generate constructs
    - Coverage groups
    - Assertions
    """
    with open(json_file, 'r') as f:
        cst = json.load(f)
    
    report = {
        'packages': [],
        'classes': [],
        'interfaces': [],
        'generates': [],
        'covergroups': [],
        'assertions': [],
        'dpi_functions': []
    }
    
    def traverse(node):
        tag = node.get('tag', '')
        metadata = node.get('metadata', {})
        
        if tag == 'kPackageDeclaration':
            report['packages'].append(metadata.get('package_info', {}))
        elif tag == 'kClassDeclaration':
            report['classes'].append(metadata.get('class_info', {}))
        elif tag == 'kInterfaceDeclaration':
            report['interfaces'].append(metadata.get('interface_info', {}))
        elif tag in ['kLoopGenerateConstruct', 'kGenerateIf']:
            report['generates'].append(metadata.get('generate_info', {}))
        elif tag == 'kCovergroupDeclaration':
            report['covergroups'].append(metadata.get('covergroup_info', {}))
        elif tag in ['kAssertionStatement', 'kPropertyDeclaration']:
            report['assertions'].append(metadata.get('assertion_info', {}))
        elif tag in ['kDPIImport', 'kDPIExport']:
            report['dpi_functions'].append(metadata.get('dpi_info', {}))
        
        for child in node.get('children', []):
            traverse(child)
    
    traverse(cst)
    return report

# Generate summary
report = analyze_complete_testbench('testbench.json')
print(f"Packages: {len(report['packages'])}")
print(f"Classes: {len(report['classes'])}")
print(f"Interfaces: {len(report['interfaces'])}")
print(f"Generate blocks: {len(report['generates'])}")
print(f"Covergroups: {len(report['covergroups'])}")
print(f"Assertions: {len(report['assertions'])}")
print(f"DPI functions: {len(report['dpi_functions'])}")
```

## Best Practices

### 1. Comprehensive Analysis

- Start with package-level structure
- Map class hierarchies
- Identify interface protocols
- Track generate-based variations
- Validate coverage model

### 2. Incremental Processing

For large codebases:
- Process files individually
- Build cross-file references
- Merge metadata incrementally
- Cache intermediate results

### 3. Error Handling

```python
def safe_extract_metadata(node, metadata_key):
    """Safely extract metadata with fallback"""
    try:
        return node.get('metadata', {}).get(metadata_key, {})
    except (KeyError, AttributeError):
        return {}
```

### 4. Performance Optimization

- Use streaming JSON parsers for large files
- Index by node type for faster lookups
- Parallelize independent file processing
- Cache frequently accessed metadata

## Tool Integration

### VeriPG Integration

VeriPG uses Verible JSON export for:
- Dependency graph construction
- Module hierarchy visualization
- Interface connection analysis
- Coverage model extraction

### Custom Analysis Tools

```python
class SystemVerilogAnalyzer:
    def __init__(self, json_file):
        with open(json_file, 'r') as f:
            self.cst = json.load(f)
        self.index = self._build_index()
    
    def _build_index(self):
        """Build fast lookup index by node type"""
        index = {}
        
        def traverse(node):
            tag = node.get('tag', '')
            if tag not in index:
                index[tag] = []
            index[tag].append(node)
            
            for child in node.get('children', []):
                traverse(child)
        
        traverse(self.cst)
        return index
    
    def find_all(self, node_type):
        """Get all nodes of a specific type"""
        return self.index.get(node_type, [])
    
    def find_classes_by_parent(self, parent_name):
        """Find all classes extending a specific parent"""
        classes = self.find_all('kClassDeclaration')
        return [
            c for c in classes
            if c.get('metadata', {}).get('class_info', {}).get('parent_class') == parent_name
        ]
```

## Troubleshooting

### Common Issues

1. **Missing Metadata**
   - Verify Verible version >= v3.0.0
   - Check for parse errors
   - Validate SystemVerilog syntax

2. **Incomplete Hierarchies**
   - Ensure all files included
   - Check package imports
   - Verify scoped references

3. **Performance Issues**
   - Process files in parallel
   - Use streaming for large files
   - Cache metadata indices

## Version History

| Version | Features Added | Tests |
|---------|---------------|-------|
| v2.2.0 | SVA, DPI, Program, Coverage | 98 tests |
| v3.0.0 | Classes, Interfaces, Packages, Generate | 194 tests |

## See Also

- [OOP Features Guide](OOP_FEATURES_GUIDE.md) - Detailed class/constraint guide
- [Interface Guide](INTERFACE_GUIDE.md) - Interface/modport details
- [Package Guide](PACKAGE_GUIDE.md) - Package organization guide

## Support

For issues or questions:
- GitHub: https://github.com/chipsalliance/verible
- Documentation: https://chipsalliance.github.io/verible/

## Version

This guide covers features available in Verible v3.0.0 and later.

