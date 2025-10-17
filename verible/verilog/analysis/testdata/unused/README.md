# EnhancedUnusedDetector Test Data

This directory contains SystemVerilog test files for validating the `EnhancedUnusedDetector` component.

## Test Categories

### Unused Signal Detection
- `unused_signals.sv` - Signals never read or written
- `write_only_signals.sv` - Signals written but never read
- `read_only_signals.sv` - Signals read but never written (undriven)

### Unused Variable Detection
- `unused_variables.sv` - Local variables never referenced
- `function_unused_vars.sv` - Function/task local variables

### Unused Function/Task Detection
- `unused_functions.sv` - Functions and tasks never called
- `called_functions.sv` - Functions that are called (should NOT be flagged)

### Unused Module Detection
- `unused_modules.sv` - Module definitions never instantiated
- `instantiated_modules.sv` - Modules with instances (should NOT be flagged)

### Dead Code Detection
- `dead_code.sv` - Unreachable code paths

### Filtering and False Positives
- `false_positives.sv` - Common false positive scenarios
- `ignore_patterns.sv` - Pattern-based filtering tests
- `port_signals.sv` - Port handling (may be intentionally unused)

### Integration Tests
- `mixed_unused.sv` - Complex real-world scenarios
- `complete_design.sv` - Full design with various unused entities

## Expected Behavior

### Unused Signals
- **Never referenced**: Should be flagged (ERROR)
- **Write-only**: Should be flagged (WARNING)
- **Read-only**: Should be flagged (WARNING - undriven signal)
- **Used signals**: Should NOT be flagged

### Unused Variables
- **Never referenced**: Should be flagged (WARNING)
- **Function parameters**: May be intentionally unused (filtered)

### Unused Functions/Tasks
- **Never called**: Should be flagged (WARNING)
- **Entry points**: Should NOT be flagged (e.g., test functions)
- **Called functions**: Should NOT be flagged

### Unused Modules
- **Never instantiated**: Should be flagged (WARNING)
- **Top-level**: Should NOT be flagged
- **Instantiated**: Should NOT be flagged

### Dead Code
- **Unreachable branches**: Should be flagged (WARNING)
- **Constant conditions**: Should be detected and flagged

## False Positive Handling

The detector should filter common false positives:
- Module ports (may be intentionally unused)
- Output ports (write-only is acceptable)
- Input ports (read-only is acceptable)
- Signals with `unused_` prefix (intentionally unused)
- Test bench signals
- Debug signals

## Integration with DataFlowAnalyzer

Tests rely on DataFlowAnalyzer to provide:
- `is_read` flag for each signal
- `is_written` flag for each signal
- Driver and reader information
- Data flow graph structure

