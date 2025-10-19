# VeriPG UVM Usage Examples

**Version**: 1.0.0  
**Verible**: v5.3.0+  
**Date**: October 2025  
**Status**: Production Ready ✅

---

## Overview

This guide provides practical examples of using Verible to analyze UVM testbenches for VeriPG integration. All examples use real-world patterns from OpenTitan and industry-standard UVM practices.

---

## Table of Contents

1. [Example 1: Simple UVM Component](#example-1-simple-uvm-component)
2. [Example 2: Parse with Package Context](#example-2-parse-with-package-context)
3. [Example 3: Extract UVM Hierarchies](#example-3-extract-uvm-hierarchies)
4. [Example 4: Constraint Analysis](#example-4-constraint-analysis)
5. [Example 5: Batch Processing](#example-5-batch-processing)

---

## Example 1: Simple UVM Component

### Goal
Parse a standalone UVM driver with explicit includes.

### Input File: `my_driver.sv`

```systemverilog
`include "uvm_macros.svh"
import uvm_pkg::*;

class my_driver extends uvm_driver #(my_transaction);
  `uvm_component_utils(my_driver)
  
  virtual my_interface vif;
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    my_transaction tr;
    forever begin
      seq_item_port.get_next_item(tr);
      drive_transaction(tr);
      seq_item_port.item_done();
    end
  endtask
  
  task drive_transaction(my_transaction tr);
    @(posedge vif.clk);
    vif.data <= tr.data;
    vif.valid <= 1'b1;
    @(posedge vif.clk);
    vif.valid <= 1'b0;
  endtask
endclass
```

### Command

```bash
verible-verilog-semantic \
  --include_kythe \
  --include_paths=third_party/uvm/src \
  my_driver.sv > driver_output.json
```

### Expected Output Structure

```json
{
  "kythe": {
    "version": "1.0.0",
    "variable_references": [
      {
        "variable_name": "tr",
        "type": "read",
        "location": {"file": "my_driver.sv", "line": 17}
      },
      {
        "variable_name": "seq_item_port",
        "type": "read",
        "location": {"file": "my_driver.sv", "line": 17}
      },
      {
        "variable_name": "vif",
        "type": "read",
        "location": {"file": "my_driver.sv", "line": 24}
      }
    ]
  }
}
```

### VeriPG Integration

```python
import json

def extract_driver_signals(json_file):
    with open(json_file) as f:
        data = json.load(f)
    
    signals = {}
    for ref in data['kythe']['variable_references']:
        name = ref['variable_name']
        if name not in signals:
            signals[name] = {'reads': 0, 'writes': 0}
        
        if ref['type'] == 'read':
            signals[name]['reads'] += 1
        elif ref['type'] == 'write':
            signals[name]['writes'] += 1
    
    return signals

# Usage
signals = extract_driver_signals('driver_output.json')
for name, counts in signals.items():
    print(f"{name}: {counts['reads']} reads, {counts['writes']} writes")
```

**Output**:
```
tr: 2 reads, 0 writes
seq_item_port: 2 reads, 0 writes
vif: 4 reads, 0 writes
```

---

## Example 2: Parse with Package Context

### Goal
Parse UVM files that don't have explicit `include` directives by parsing the package file.

### Real-World Scenario: OpenTitan AES

**Problem**: File `aes_env.sv` uses `uvm_component_utils` but doesn't include `uvm_macros.svh` directly.

**Solution**: Parse the package file that includes all dependencies.

### Directory Structure

```
hw/ip/aes/dv/
├── env/
│   ├── aes_env.sv           ← Target file (no explicit includes)
│   ├── aes_scoreboard.sv
│   └── aes_env_pkg.sv       ← Package file (has all includes)
└── tb/
    └── tb.sv
```

### Package File: `aes_env_pkg.sv`

```systemverilog
package aes_env_pkg;
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import cip_lib_pkg::*;
  
  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  
  // Include all environment files
  `include "aes_env_cfg.sv"
  `include "aes_env_cov.sv"
  `include "aes_scoreboard.sv"
  `include "aes_env.sv"         ← Target included here
endpackage
```

### Command (Recommended)

```bash
# Parse the PACKAGE file, not the individual file
verible-verilog-semantic \
  --include_kythe \
  --include_paths=third_party/uvm/src,hw/dv/sv/dv_utils,hw/dv/sv/cip_lib \
  hw/ip/aes/dv/env/aes_env_pkg.sv > aes_output.json
```

### Why This Works

1. Package file includes `uvm_macros.svh` at the top
2. All macros are defined before being used
3. Full context available for preprocessing
4. Matches how UVM files are actually compiled

### Alternative (Less Reliable)

```bash
# Parsing individual file - may fail if macros not defined
verible-verilog-semantic \
  --include_kythe \
  --include_paths=third_party/uvm/src,hw/dv/sv \
  hw/ip/aes/dv/env/aes_env.sv > aes_output.json
```

⚠️ **Note**: Individual file parsing works ONLY if the file has explicit `include` directives.

---

## Example 3: Extract UVM Hierarchies

### Goal
Build a complete UVM testbench hierarchy map.

### Input: OpenTitan UART Testbench

```bash
# Parse the entire UART environment package
verible-verilog-semantic \
  --include_kythe \
  --include_paths=third_party/uvm/src,hw/dv/sv/dv_utils,hw/dv/sv/cip_lib \
  hw/ip/uart/dv/env/uart_env_pkg.sv > uart_hierarchy.json
```

### Python Script: `extract_uvm_hierarchy.py`

```python
import json
from collections import defaultdict

def extract_uvm_hierarchy(json_file):
    """Extract UVM component relationships from Kythe facts."""
    
    with open(json_file) as f:
        data = json.load(f)
    
    # Build component map
    components = defaultdict(lambda: {
        'type': 'unknown',
        'file': '',
        'line': 0,
        'signals': [],
        'methods': []
    })
    
    # Extract from variable references
    for ref in data.get('kythe', {}).get('variable_references', []):
        var_name = ref['variable_name']
        
        # Identify UVM components
        if 'env' in var_name or 'agent' in var_name or \
           'driver' in var_name or 'monitor' in var_name or \
           'sequencer' in var_name or 'scoreboard' in var_name:
            
            components[var_name]['file'] = ref['location']['file']
            components[var_name]['line'] = ref['location']['line']
            components[var_name]['signals'].append({
                'name': var_name,
                'type': ref['type'],
                'line': ref['location']['line']
            })
    
    return dict(components)

def print_hierarchy(components):
    """Print UVM hierarchy in tree format."""
    
    print("UVM Testbench Hierarchy")
    print("=" * 60)
    
    # Group by component type
    types = defaultdict(list)
    for name, info in components.items():
        comp_type = 'unknown'
        if 'env' in name: comp_type = 'Environment'
        elif 'agent' in name: comp_type = 'Agent'
        elif 'driver' in name: comp_type = 'Driver'
        elif 'monitor' in name: comp_type = 'Monitor'
        elif 'sequencer' in name: comp_type = 'Sequencer'
        elif 'scoreboard' in name: comp_type = 'Scoreboard'
        
        types[comp_type].append((name, info))
    
    # Print by type
    for comp_type in ['Environment', 'Agent', 'Sequencer', 'Driver', 'Monitor', 'Scoreboard']:
        if comp_type in types:
            print(f"\n{comp_type}s:")
            for name, info in sorted(types[comp_type]):
                print(f"  - {name}")
                print(f"    File: {info['file']}:{info['line']}")
                print(f"    Signals: {len(info['signals'])}")

# Usage
components = extract_uvm_hierarchy('uart_hierarchy.json')
print_hierarchy(components)
```

### Expected Output

```
UVM Testbench Hierarchy
============================================================

Environments:
  - uart_env
    File: hw/ip/uart/dv/env/uart_env.sv:15
    Signals: 8

Agents:
  - uart_agent
    File: hw/ip/uart/dv/env/uart_agent.sv:12
    Signals: 5

Sequencers:
  - uart_sequencer
    File: hw/ip/uart/dv/env/uart_sequencer.sv:10
    Signals: 2

Drivers:
  - uart_driver
    File: hw/ip/uart/dv/env/uart_driver.sv:20
    Signals: 12

Monitors:
  - uart_monitor
    File: hw/ip/uart/dv/env/uart_monitor.sv:18
    Signals: 10

Scoreboards:
  - uart_scoreboard
    File: hw/ip/uart/dv/env/uart_scoreboard.sv:25
    Signals: 15
```

---

## Example 4: Constraint Analysis

### Goal
Extract constraint blocks for formal verification or coverage analysis.

### Input File: `constrained_seq.sv`

```systemverilog
class my_sequence extends uvm_sequence #(my_transaction);
  `uvm_object_utils(my_sequence)
  
  rand int addr;
  rand int data;
  
  constraint addr_range {
    addr inside {[0:255]};
  }
  
  constraint data_dist {
    data dist {
      [0:10]    := 50,
      [11:100]  := 30,
      [101:255] := 20
    };
  }
  
  `uvm_object_new
endclass
```

### Command

```bash
verible-verilog-semantic \
  --include_kythe \
  --include_paths=third_party/uvm/src \
  constrained_seq.sv > constraints.json
```

### Python Script: `extract_constraints.py`

```python
import json
import re

def extract_constraints(json_file):
    """Extract constraint information from parsed SystemVerilog."""
    
    with open(json_file) as f:
        data = json.load(f)
    
    constraints = []
    
    # Extract variables referenced in constraints
    for ref in data.get('kythe', {}).get('variable_references', []):
        var_name = ref['variable_name']
        
        # Heuristic: Variables read in specific line ranges might be in constraints
        # (More sophisticated parsing would use CST analysis)
        constraints.append({
            'variable': var_name,
            'location': f"{ref['location']['file']}:{ref['location']['line']}",
            'type': ref['type']
        })
    
    return constraints

# Usage
constraints = extract_constraints('constraints.json')
print(f"Found {len(constraints)} constraint references")
for c in constraints:
    print(f"  {c['variable']} at {c['location']}")
```

---

## Example 5: Batch Processing

### Goal
Process all UVM files in an OpenTitan project.

### Bash Script: `batch_uvm_analysis.sh`

```bash
#!/bin/bash

# Configuration
VERIBLE_BIN="bazel-bin/verible/verilog/tools/semantic/verible-verilog-semantic"
OUTPUT_DIR="build/uvm_analysis"
UVM_PATHS="third_party/uvm/src,hw/dv/sv/dv_utils,hw/dv/sv/cip_lib"

mkdir -p "$OUTPUT_DIR"

# Find all *_pkg.sv files (package files)
PKG_FILES=$(find hw/ip -name "*_pkg.sv" | grep "/dv/")

TOTAL=$(echo "$PKG_FILES" | wc -l)
CURRENT=0
SUCCESS=0
FAILED=0

echo "Processing $TOTAL UVM package files..."

for pkg_file in $PKG_FILES; do
  CURRENT=$((CURRENT + 1))
  
  # Extract module name
  MODULE=$(basename $(dirname $(dirname $pkg_file)))
  OUTPUT_FILE="$OUTPUT_DIR/${MODULE}_analysis.json"
  
  echo -ne "[$CURRENT/$TOTAL] Processing $MODULE... "
  
  # Run analysis
  if $VERIBLE_BIN \
      --include_kythe \
      --include_paths=$UVM_PATHS \
      "$pkg_file" > "$OUTPUT_FILE" 2>/dev/null; then
    
    SUCCESS=$((SUCCESS + 1))
    echo "✅"
  else
    FAILED=$((FAILED + 1))
    echo "❌"
    rm -f "$OUTPUT_FILE"
  fi
done

echo ""
echo "Results:"
echo "  Success: $SUCCESS/$TOTAL"
echo "  Failed:  $FAILED/$TOTAL"
echo "  Output:  $OUTPUT_DIR/"
```

### Usage

```bash
chmod +x batch_uvm_analysis.sh
./batch_uvm_analysis.sh
```

### Python Post-Processing: `aggregate_results.py`

```python
import json
import glob
from collections import defaultdict

def aggregate_results(output_dir):
    """Aggregate results from batch processing."""
    
    all_components = defaultdict(int)
    all_signals = defaultdict(int)
    
    json_files = glob.glob(f"{output_dir}/*.json")
    
    for json_file in json_files:
        with open(json_file) as f:
            data = json.load(f)
        
        module = json_file.split('/')[-1].replace('_analysis.json', '')
        
        refs = data.get('kythe', {}).get('variable_references', [])
        
        all_components[module] = len(refs)
        
        for ref in refs:
            var_type = ref.get('type', 'unknown')
            all_signals[var_type] += 1
    
    return all_components, all_signals

def print_summary(components, signals):
    """Print aggregated summary."""
    
    print("\nAggregate Analysis Summary")
    print("=" * 60)
    print(f"\nTotal Modules Analyzed: {len(components)}")
    print(f"Total Signal References: {sum(components.values())}")
    
    print("\nSignal Types:")
    for sig_type, count in sorted(signals.items()):
        print(f"  {sig_type}: {count}")
    
    print("\nTop 10 Modules by Signal Count:")
    top_modules = sorted(components.items(), key=lambda x: x[1], reverse=True)[:10]
    for module, count in top_modules:
        print(f"  {module}: {count}")

# Usage
components, signals = aggregate_results('build/uvm_analysis')
print_summary(components, signals)
```

### Expected Output

```
Aggregate Analysis Summary
============================================================

Total Modules Analyzed: 42
Total Signal References: 3,847

Signal Types:
  read: 2,105
  write: 1,512
  read_write: 230

Top 10 Modules by Signal Count:
  aes: 342
  uart: 298
  spi_device: 275
  i2c: 241
  gpio: 198
  ...
```

---

## Best Practices

### 1. Always Use Package Files

✅ **Recommended**:
```bash
verible-verilog-semantic --include_kythe my_env_pkg.sv
```

❌ **Avoid**:
```bash
verible-verilog-semantic --include_kythe my_env.sv  # May fail
```

### 2. Specify Include Paths

Always provide paths to:
- UVM library: `third_party/uvm/src`
- Project utilities: `hw/dv/sv/dv_utils`
- Common libraries: `hw/dv/sv/cip_lib`

### 3. Check Preprocessing Status

```bash
# Verify preprocessing is enabled (default: true)
verible-verilog-semantic --help | grep preprocess
```

### 4. Handle Errors Gracefully

```python
def safe_parse(file_path):
    try:
        result = subprocess.run(
            ['verible-verilog-semantic', '--include_kythe', file_path],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if result.returncode == 0:
            return json.loads(result.stdout)
        else:
            print(f"Error parsing {file_path}: {result.stderr}")
            return None
    except Exception as e:
        print(f"Exception: {e}")
        return None
```

---

## Troubleshooting

### Issue: "preprocessing error at token \`uvm_component_utils\`"

**Solution**: Parse the package file instead:
```bash
find . -name "*_pkg.sv" | xargs grep -l "my_component"
verible-verilog-semantic --include_kythe found_package.sv
```

### Issue: Empty `kythe.variable_references` array

**Possible Causes**:
1. File has no variable references (check parse tree)
2. Preprocessing failed (check stderr)
3. File is pure declarations (expected)

**Debug**:
```bash
# Check if file parses at all
verible-verilog-syntax my_file.sv

# Check preprocessing
verible-verilog-preprocessor --include_paths=... my_file.sv
```

### Issue: Performance slow on large files

**Solutions**:
1. Use batch processing with parallelization
2. Process package files instead of individual files
3. Filter output to only needed facts

---

## Next Steps

1. **Integration**: Integrate these patterns into VeriPG's analysis pipeline
2. **Automation**: Use batch processing scripts for large projects
3. **Validation**: Compare extracted facts against known testbench structures
4. **Enhancement**: Extend Python scripts for VeriPG-specific needs

---

## References

- **Verible Documentation**: `verible/verilog/tools/semantic/README.md`
- **UVM Capabilities**: `UVM_CAPABILITIES_REALITY.md`
- **Integration Guide**: `VERIPG_INTEGRATION_GUIDE.md`
- **Release Notes**: `RELEASE_NOTES_v5.3.0.md`

---

**Questions?** See `VERIPG_INTEGRATION_GUIDE.md` Troubleshooting section or OpenTitan analysis in `OPENTITAN_PARSING_ANALYSIS.md`.
