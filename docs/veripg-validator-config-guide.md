# VeriPG Validator Configuration Guide

**Version 5.0.0** | Complete guide to configuring validation rules

## Table of Contents

1. [Overview](#overview)
2. [Configuration File Format](#configuration-file-format)
3. [Global Settings](#global-settings)
4. [Rule Configuration](#rule-configuration)
5. [File Exclusions](#file-exclusions)
6. [Advanced Configuration](#advanced-configuration)
7. [Configuration Examples](#configuration-examples)

---

## Overview

VeriPG Validator uses YAML or JSON configuration files to customize validation behavior. Configuration files allow you to:

- Enable/disable specific rules
- Set rule severity levels
- Exclude files or modules from validation
- Configure rule-specific parameters
- Control auto-fix behavior
- Optimize performance settings

---

## Configuration File Format

### File Location Priority

The validator searches for configuration in this order:

1. File specified with `--config` flag
2. `.veripg.yml` in current directory
3. `.veripg.json` in current directory
4. `~/.veripg.yml` in home directory
5. Default configuration (all rules enabled)

### YAML Format (Recommended)

```yaml
# .veripg.yml
severity: warning
rules:
  CDC_001:
    enabled: true
    severity: error
```

### JSON Format

```json
{
  "severity": "warning",
  "rules": {
    "CDC_001": {
      "enabled": true,
      "severity": "error"
    }
  }
}
```

---

## Global Settings

### Default Severity

Set the minimum severity level to report:

```yaml
severity: warning  # Options: error, warning, info
```

- `error`: Report only errors
- `warning`: Report errors and warnings (default)
- `info`: Report all violations including informational

### Output Format

```yaml
output:
  format: text  # Options: text, json, sarif
  colorize: true
  verbose: false
```

### Performance Settings

```yaml
performance:
  cache_enabled: true
  parallel_processing: true
  max_threads: 8
  incremental: false
```

---

## Rule Configuration

### Basic Rule Configuration

Each rule can be configured individually:

```yaml
rules:
  CDC_001:  # Rule ID
    enabled: true       # Enable/disable rule
    severity: error     # Override severity: error, warning, info
```

### Disable Specific Rules

```yaml
rules:
  NAM_001:
    enabled: false  # Disable module naming checks
  
  NAM_002:
    enabled: false  # Disable signal name length checks
```

### Override Rule Severity

```yaml
rules:
  CLK_001:
    severity: error  # Upgrade from warning to error
  
  STR_002:
    severity: info   # Downgrade from warning to info
```

### Rule-Specific Parameters

Some rules accept custom parameters:

```yaml
rules:
  NAM_001:
    enabled: true
    parameters:
      style: "snake_case"  # Enforce lowercase_with_underscores
  
  NAM_002:
    enabled: true
    parameters:
      min_length: 3  # Minimum signal name length
  
  NAM_003:
    enabled: true
    parameters:
      style: "UPPER_CASE"  # Parameter naming
  
  STR_002:
    enabled: true
    parameters:
      max_statements: 50  # Complexity threshold
  
  STR_003:
    enabled: true
    parameters:
      max_hierarchy_depth: 5
```

### Per-Rule Exclusions

Exclude specific files or modules from a rule:

```yaml
rules:
  CDC_001:
    enabled: true
    severity: error
    exclusions:
      - "testbench/**"
      - "*_tb.sv"
      - "vendor/legacy_module.sv"
```

---

## File Exclusions

### Global Exclusions

Apply exclusions to all rules:

```yaml
exclusions:
  - "vendor/**"           # Exclude vendor directory
  - "third_party/**"      # Exclude third-party code
  - "**/*_tb.sv"          # Exclude all testbenches
  - "**/*_test.sv"        # Exclude test files
  - "sim/**"              # Exclude simulation files
```

### Glob Pattern Syntax

- `*`: Match any characters except `/`
- `**`: Match any characters including `/` (recursive)
- `?`: Match single character
- `[abc]`: Match one of a, b, or c
- `{a,b}`: Match a or b

**Examples:**

```yaml
exclusions:
  - "*.vh"                # All header files
  - "rtl/**/generated_*.sv"  # Generated files in rtl tree
  - "test_*.sv"           # Files starting with test_
  - "legacy_[0-9].sv"     # legacy_0.sv through legacy_9.sv
```

---

## Advanced Configuration

### Auto-Fix Configuration

```yaml
auto_fix:
  enable_safe_fixes: true      # Auto-apply safe fixes
  enable_unsafe_fixes: false   # Require manual review for unsafe fixes
  backup_originals: true       # Create .bak files before modifying
  
  # Configure which fix categories are considered safe
  safe_categories:
    - naming              # Naming convention fixes
    - formatting          # Code formatting
    - default_clause      # Adding default to case statements
  
  # Require manual review for these
  unsafe_categories:
    - cdc_synchronizer    # CDC fixes
    - reset_addition      # Reset signal modifications
    - width_conversion    # Width casting
```

### Batch Processing Configuration

```yaml
batch:
  enabled: true
  progress_reporting: true
  parallel: true
  max_parallel_files: 8
  continue_on_error: true
```

### Caching Configuration

```yaml
cache:
  enabled: true
  type_inference: true
  clock_domains: true
  reset_signals: true
  cache_dir: ".veripg_cache"
  ttl_hours: 24
```

---

## Configuration Examples

### Minimal Configuration

Enable only critical CDC and clock rules:

```yaml
# .veripg.yml
severity: error

rules:
  CDC_001:
    enabled: true
  CDC_002:
    enabled: true
  CLK_002:
    enabled: true

# Disable all other rules
default:
  enabled: false
```

### Strict Configuration

Maximum strictness for production code:

```yaml
# .veripg-strict.yml
severity: info  # Report everything

rules:
  # All CDC/Clock/Reset rules as errors
  CDC_001: { enabled: true, severity: error }
  CDC_002: { enabled: true, severity: error }
  CDC_003: { enabled: true, severity: error }
  CDC_004: { enabled: true, severity: error }
  CLK_001: { enabled: true, severity: error }
  CLK_002: { enabled: true, severity: error }
  CLK_003: { enabled: true, severity: error }
  CLK_004: { enabled: true, severity: error }
  RST_001: { enabled: true, severity: error }
  RST_002: { enabled: true, severity: error }
  RST_003: { enabled: true, severity: error }
  RST_004: { enabled: true, severity: error }
  TIM_001: { enabled: true, severity: error }
  TIM_002: { enabled: true, severity: error }
  
  # All naming rules as warnings
  NAM_001: { enabled: true, severity: warning }
  NAM_002: { enabled: true, severity: warning }
  NAM_003: { enabled: true, severity: warning }
  NAM_004: { enabled: true, severity: warning }
  NAM_005: { enabled: true, severity: warning }
  NAM_006: { enabled: true, severity: warning }
  NAM_007: { enabled: true, severity: error }
  
  # Width checking as errors
  WID_001: { enabled: true, severity: error }
  WID_002: { enabled: true, severity: error }
  WID_003: { enabled: true, severity: error }
  WID_004: { enabled: true, severity: warning }
  WID_005: { enabled: true, severity: error }

exclusions:
  - "testbench/**"

auto_fix:
  enable_safe_fixes: false  # Manual review for all fixes
```

### Lenient Configuration

For legacy code or initial adoption:

```yaml
# .veripg-lenient.yml
severity: error  # Only show critical issues

rules:
  # Enable only the most critical rules
  CDC_001: { enabled: true, severity: error }
  CDC_002: { enabled: true, severity: error }
  CLK_002: { enabled: true, severity: error }
  TIM_001: { enabled: true, severity: error }
  WID_001: { enabled: true, severity: error }
  WID_005: { enabled: true, severity: error }

# Disable naming and structural rules
rules:
  NAM_001: { enabled: false }
  NAM_002: { enabled: false }
  NAM_003: { enabled: false }
  STR_001: { enabled: false }
  STR_002: { enabled: false }

exclusions:
  - "legacy/**"
  - "vendor/**"
  - "testbench/**"
```

### Team-Specific Configuration

Different configurations for different teams:

```yaml
# .veripg-frontend.yml (Frontend team)
rules:
  # Strict on naming for frontend
  NAM_001: { enabled: true, severity: error }
  NAM_002: { enabled: true, severity: warning }
  NAM_003: { enabled: true, severity: error }
  
  # Relaxed on structure
  STR_002: { enabled: false }
  STR_003: { enabled: false }

exclusions:
  - "backend/**"  # Don't check backend code
```

```yaml
# .veripg-backend.yml (Backend team)
rules:
  # Strict on CDC/timing for backend
  CDC_001: { enabled: true, severity: error }
  CDC_002: { enabled: true, severity: error }
  TIM_001: { enabled: true, severity: error }
  
  # Relaxed on naming
  NAM_001: { enabled: false }
  NAM_002: { enabled: false }

exclusions:
  - "frontend/**"  # Don't check frontend code
```

### Project-Specific Naming Standards

```yaml
# .veripg-custom-naming.yml
rules:
  NAM_001:
    enabled: true
    parameters:
      style: "snake_case"
      exceptions:
        - "CRC_*"  # Allow CRC prefix
        - "USB_*"  # Allow USB prefix
  
  NAM_004:
    enabled: true
    parameters:
      allowed_prefixes:
        - "clk_"
        - "clock_"
        - "sysclk_"
  
  NAM_005:
    enabled: true
    parameters:
      allowed_prefixes:
        - "rst_"
        - "rstn_"
        - "reset_"
      allowed_suffixes:
        - "_n"
        - "_rst"
        - "_reset"
```

---

## Configuration Validation

Validate your configuration file:

```bash
veripg-validator --config=.veripg.yml --check-config
```

This will:
- Parse the configuration file
- Validate rule IDs
- Check parameter syntax
- Report any errors or warnings

---

## Environment Variables

Override configuration with environment variables:

```bash
export VERIPG_CONFIG=/path/to/config.yml
export VERIPG_SEVERITY=error
export VERIPG_FORMAT=json
export VERIPG_PARALLEL=8

veripg-validator design.sv
```

---

## Best Practices

1. **Start lenient, gradually tighten**: Begin with only critical rules enabled, add more over time
2. **Use team-specific configs**: Different validation for frontend/backend/testbench code
3. **Version control your config**: Commit `.veripg.yml` to your repository
4. **Document exceptions**: Comment why specific rules are disabled
5. **Regular reviews**: Periodically review and update configuration
6. **CI/CD consistency**: Use same config in CI as local development

---

## Troubleshooting

### Configuration Not Loading

```bash
# Verify which config file is being used
veripg-validator --show-config design.sv
```

### Rule Not Working as Expected

```bash
# Check rule configuration
veripg-validator --show-rule-config CDC_001
```

### Exclusions Not Working

Verify glob patterns match your files:

```bash
# Test exclusion patterns
veripg-validator --test-exclusion "testbench/**/*.sv"
```

---

For more information:
- [User Guide](./veripg-validator-user-guide.md)
- [Rules Reference](./veripg-validator-rules-reference.md)
- [Auto-Fix Guide](./veripg-validator-autofix-guide.md)

