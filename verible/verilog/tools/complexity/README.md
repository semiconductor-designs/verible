# Code Complexity Analyzer

## Overview

`verible-verilog-complexity` analyzes SystemVerilog code complexity using call graph metrics, cyclomatic complexity, and other quality indicators.

## Features

- **Cyclomatic Complexity** - Decision point analysis
- **Call Depth Analysis** - Maximum call chain depth
- **Function Size Metrics** - Lines of code per function
- **Dependency Analysis** - Fan-in/fan-out metrics
- **Multiple Formats** - Text, JSON, HTML output

## Usage

```bash
# Text report (default)
verible-verilog-complexity design.sv

# JSON format
verible-verilog-complexity --format=json design.sv

# HTML format
verible-verilog-complexity --format=html design.sv > report.html
```

## Report Contents

### Text Format
```
Complexity Analysis Report
==========================

Total Functions: 25
Average Complexity: 4
Max Complexity: 12
Most Complex: process_data

Per-Function Metrics:
- main_loop: complexity=8, depth=3, size=45
- helper_func: complexity=2, depth=1, size=12
```

### JSON Format
```json
{
  "total_functions": 25,
  "average_complexity": 4,
  "max_complexity": 12,
  "most_complex_function": "process_data",
  "per_function": {
    "main_loop": {
      "cyclomatic_complexity": 8,
      "call_depth": 3,
      "function_size": 45
    }
  }
}
```

## Metrics Explained

### Cyclomatic Complexity
Number of linearly independent paths through code. Higher = more complex.

- **1-10:** Simple, easy to test
- **11-20:** Moderate complexity
- **21+:** High complexity, consider refactoring

### Call Depth
Maximum depth of function call chains. Deeper = harder to understand.

### Fan-in / Fan-out
- **Fan-in:** How many functions call this function
- **Fan-out:** How many functions this function calls

## Development Status

**Version:** 0.1.0  
**Test Coverage:** 15/15 tests passing

## See Also

- [Call Graph Documentation](../../analysis/call-graph.h)
- [Dead Code Tool](../deadcode/README.md)

