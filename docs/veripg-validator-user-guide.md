# VeriPG Validator User Guide

## Table of Contents
1. [Introduction](#introduction)
2. [Installation](#installation)
3. [Quick Start](#quick-start)
4. [Usage](#usage)
5. [Configuration](#configuration)
6. [Understanding Violations](#understanding-violations)
7. [Auto-Fix System](#auto-fix-system)
8. [Batch Mode](#batch-mode)
9. [CI/CD Integration](#cicd-integration)
10. [Troubleshooting](#troubleshooting)

## Introduction

VeriPG Validator is a comprehensive SystemVerilog style checker and validation tool that helps identify design issues, coding standard violations, and potential bugs in your RTL code.

### Key Features

- **39+ validation rules** across 7 categories:
  - Clock Domain Crossing (CDC)
  - Clock handling (CLK)
  - Reset handling (RST)
  - Timing analysis (TIM)
  - Naming conventions (NAM)
  - Width checking (WID)
  - Power intent (PWR)
  - Structure (STR)

- **Auto-fix suggestions** for common violations
- **Multiple output formats**: Text, JSON, SARIF
- **Configurable rules**: Enable/disable, set severity, define exclusions
- **Batch processing**: Validate entire projects
- **CI/CD ready**: GitHub Actions, GitLab CI, Jenkins templates

## Installation

### From Verible Release

1. Download the latest Verible release from:
   ```
   https://github.com/chipsalliance/verible/releases
   ```

2. Extract the archive:
   ```bash
   tar -xzf verible-*.tar.gz
   ```

3. Add to PATH:
   ```bash
   export PATH="/path/to/verible/bin:$PATH"
   ```

4. Verify installation:
   ```bash
   veripg-validator --version
   ```

### From Source

See [Building From Source](./building-from-source.md) for detailed instructions.

## Quick Start

### Basic Usage

Validate a single SystemVerilog file:
```bash
veripg-validator my_module.sv
```

### Validate Multiple Files

```bash
veripg-validator rtl/**/*.sv
```

### Generate JSON Output

```bash
veripg-validator --format=json --output=report.json rtl/**/*.sv
```

### Example Output

```
VeriPG Validation Report
========================

Summary:
  Errors:   2
  Warnings: 5
  Info:     1
  Total:    8

Violations:
-----------

[ERROR] CDC_001: CDC without synchronizer
  Signal: async_data
  Location: rtl/top.sv:45:10
  Suggestion: Add 2-stage synchronizer: always_ff @(posedge clk) begin sync_data <= {sync_data[0], async_data}; end

[WARNING] CLK_001: Missing clock signal in always_ff
  Signal: data_reg
  Location: rtl/fifo.sv:78:5
  Suggestion: Add clock to sensitivity list: always_ff @(posedge clk)
```

## Usage

### Command-Line Options

```
veripg-validator [OPTIONS] <files...>

Options:
  --format=FORMAT          Output format: text, json, sarif (default: text)
  --output=FILE            Write output to file (default: stdout)
  --config=FILE            Configuration file (default: .veripg.yml)
  --batch                  Enable batch mode with progress reporting
  --parallel=N             Use N threads for parallel validation (default: 4)
  --rules=RULES            Comma-separated list of rules to enable
  --disable=RULES          Comma-separated list of rules to disable
  --severity=LEVEL         Minimum severity to report: error, warning, info
  --auto-fix               Generate auto-fix suggestions
  --apply-fixes            Apply safe auto-fixes automatically (use with caution)
  --help                   Show this help message
  --version                Show version information
```

### Examples

**Validate with specific rules:**
```bash
veripg-validator --rules=CDC_001,CLK_001,RST_001 design.sv
```

**Disable specific rules:**
```bash
veripg-validator --disable=NAM_001,NAM_002 design.sv
```

**Show only errors:**
```bash
veripg-validator --severity=error rtl/**/*.sv
```

**Generate SARIF for CI/CD:**
```bash
veripg-validator --format=sarif --output=veripg.sarif rtl/**/*.sv
```

**Batch mode with progress:**
```bash
veripg-validator --batch --parallel=8 rtl/**/*.sv
```

## Configuration

VeriPG Validator can be configured using a YAML or JSON configuration file.

### Configuration File Location

The validator looks for configuration files in this order:
1. File specified with `--config` flag
2. `.veripg.yml` in current directory
3. `.veripg.json` in current directory
4. `~/.veripg.yml` in home directory

### Example Configuration (.veripg.yml)

```yaml
# VeriPG Validator Configuration

# Global settings
severity: warning  # Minimum severity to report: error, warning, info

# Rule configuration
rules:
  # CDC rules
  CDC_001:
    enabled: true
    severity: error
    exclusions:
      - "testbench/**"
      - "*_tb.sv"
  
  CDC_002:
    enabled: true
    severity: error
  
  # Clock rules
  CLK_001:
    enabled: true
    severity: warning
  
  CLK_002:
    enabled: true
    severity: error
  
  # Naming rules
  NAM_001:
    enabled: true
    severity: warning
    parameters:
      style: "snake_case"  # lowercase_with_underscores
  
  NAM_002:
    enabled: true
    severity: info
    parameters:
      min_length: 3
  
  NAM_003:
    enabled: true
    severity: warning
    parameters:
      style: "UPPER_CASE"
  
  # Width rules
  WID_001:
    enabled: true
    severity: error
  
  WID_002:
    enabled: true
    severity: warning
  
  # Structure rules
  STR_002:
    enabled: true
    severity: warning
    parameters:
      max_statements: 50  # Complexity threshold
  
  STR_003:
    enabled: true
    severity: warning
    parameters:
      max_hierarchy_depth: 5

# File/module exclusions (apply to all rules)
exclusions:
  - "vendor/**"
  - "third_party/**"
  - "**/*_tb.sv"
  - "**/*_test.sv"

# Auto-fix settings
auto_fix:
  enable_safe_fixes: true
  enable_unsafe_fixes: false  # Require manual review

# Performance settings
performance:
  cache_enabled: true
  parallel_processing: true
  max_threads: 8
```

### JSON Configuration Format

```json
{
  "severity": "warning",
  "rules": {
    "CDC_001": {
      "enabled": true,
      "severity": "error"
    },
    "CLK_001": {
      "enabled": true,
      "severity": "warning"
    }
  },
  "exclusions": [
    "testbench/**",
    "**/*_tb.sv"
  ]
}
```

## Understanding Violations

Each violation report includes:

1. **Severity**: Error, Warning, or Info
2. **Rule ID**: Unique identifier (e.g., CDC_001)
3. **Message**: Description of the violation
4. **Signal name**: Affected signal (if applicable)
5. **Location**: File path and line:column
6. **Fix suggestion**: Recommended fix (if available)

### Severity Levels

- **Error**: Critical issues that can cause functional bugs
- **Warning**: Potential issues or style violations
- **Info**: Informational messages about code quality

### Rule Categories

- **CDC (Clock Domain Crossing)**: Synchronization and metastability issues
- **CLK (Clock)**: Clock signal usage and sensitivity lists
- **RST (Reset)**: Reset signal handling
- **TIM (Timing)**: Combinational loops and latch inference
- **NAM (Naming)**: Naming convention violations
- **WID (Width)**: Signal width mismatches
- **PWR (Power)**: Power intent annotations
- **STR (Structure)**: Module structure and complexity

## Auto-Fix System

VeriPG Validator provides automated fix suggestions for many violations.

### Safe vs Unsafe Fixes

**Safe fixes** (automatically applicable):
- Naming convention fixes (snake_case, UPPER_CASE)
- Port ordering
- Adding default clauses to case statements
- Clock signal additions to sensitivity lists

**Unsafe fixes** (require manual review):
- CDC synchronizer insertion
- Reset signal additions
- Width conversion
- Structural changes

### Generating Fix Suggestions

```bash
veripg-validator --auto-fix design.sv
```

### Applying Safe Fixes Automatically

```bash
veripg-validator --auto-fix --apply-fixes design.sv
```

**⚠️ Warning**: Always review changes and test thoroughly after applying auto-fixes.

### Fix Examples

**NAM_001: Module naming**
```systemverilog
// Before
module MyModule;
endmodule

// After (auto-fix)
module my_module;
endmodule
```

**CLK_001: Missing clock**
```systemverilog
// Before
always_ff begin
  data_reg <= data_in;
end

// After (suggested fix)
always_ff @(posedge clk) begin
  data_reg <= data_in;
end
```

## Batch Mode

For large projects, use batch mode for efficient validation:

```bash
veripg-validator --batch --parallel=8 --output=report.json rtl/**/*.sv
```

### Batch Mode Features

- **Progress reporting**: Real-time feedback on validation progress
- **Parallel processing**: Utilize multiple CPU cores
- **Summary statistics**: Total files, violations, timing
- **Per-file timing**: Identify slow-to-validate files

### Example Batch Output

```
Validating 150 files with 8 threads...
[====================] 100% (150/150 files)

Batch Validation Summary
========================
Total files processed: 150
Files with violations: 23
Total violations: 87
Failed files: 0
Total time: 12.34 s

Average time per file: 82 ms
```

## CI/CD Integration

VeriPG Validator integrates seamlessly with popular CI/CD platforms.

### GitHub Actions

See [ci/github-actions-example.yml](../verible/verilog/tools/veripg/ci/github-actions-example.yml)

```yaml
- name: Run VeriPG Validator
  run: |
    veripg-validator \
      --format=sarif \
      --output=veripg.sarif \
      rtl/**/*.sv

- name: Upload SARIF
  uses: github/codeql-action/upload-sarif@v2
  with:
    sarif_file: veripg.sarif
```

### GitLab CI

See [ci/gitlab-ci-example.yml](../verible/verilog/tools/veripg/ci/gitlab-ci-example.yml)

### Jenkins

See [ci/jenkins-example.groovy](../verible/verilog/tools/veripg/ci/jenkins-example.groovy)

### Exit Codes

- `0`: No errors found (warnings may be present)
- `1`: Errors found or validation failed
- `2`: Invalid command-line arguments

## Troubleshooting

### Common Issues

**1. "No violations found" but I expected some**

Check your configuration file. Rules may be disabled or excluded.

```bash
veripg-validator --config=/dev/null design.sv  # Use default config
```

**2. Slow validation for large files**

Enable caching and parallel processing:

```bash
veripg-validator --parallel=8 --batch design.sv
```

**3. False positives**

Exclude specific files or modules in `.veripg.yml`:

```yaml
exclusions:
  - "path/to/false_positive.sv"
```

Or disable specific rules:

```bash
veripg-validator --disable=NAM_001 design.sv
```

**4. Parsing errors**

VeriPG Validator uses Verible's SystemVerilog parser. If you encounter parsing errors, ensure your code is valid SystemVerilog 2017/2023.

### Getting Help

- GitHub Issues: https://github.com/chipsalliance/verible/issues
- Documentation: https://github.com/chipsalliance/verible/tree/master/docs
- Rules Reference: [veripg-validator-rules-reference.md](./veripg-validator-rules-reference.md)

## Next Steps

- Read the [Rules Reference](./veripg-validator-rules-reference.md) for detailed rule documentation
- See [Configuration Guide](./veripg-validator-config-guide.md) for advanced configuration
- Check out [Example Projects](./veripg-validator-examples/) for real-world usage

---

**VeriPG Validator v5.0.0** | Part of the Verible SystemVerilog Toolkit

