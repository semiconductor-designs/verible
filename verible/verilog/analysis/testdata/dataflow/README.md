# DataFlowAnalyzer Test Data

This directory contains SystemVerilog test files for validating the `DataFlowAnalyzer` component.

## Test Categories

### Basic Data Flow
- `simple_assignment.sv` - Basic wire and continuous assignments
- `blocking_assignment.sv` - Blocking assignments in always blocks
- `nonblocking_assignment.sv` - Non-blocking assignments in sequential logic
- `chained_assignments.sv` - Multi-level data flow chains

### Multi-Driver Detection
- `multi_driver_conflict.sv` - Multiple drivers causing conflicts
- `conditional_drivers.sv` - Mutually exclusive conditional drivers
- `bidirectional_port.sv` - Inout ports with multiple drivers (legal)

### Dependency Analysis
- `dependency_chain.sv` - Transitive dependency relationships
- `circular_dependency.sv` - Combinational feedback loops
- `cross_module_dependency.sv` - Data flow across module boundaries

### Constant Propagation
- `constant_propagation.sv` - Parameters and constant assignments
- `parameter_usage.sv` - Parameter usage in expressions

### Edge Cases
- `empty_module.sv` - Module with no signals
- `unconnected_signals.sv` - Signals with no drivers or readers
- `complex_dataflow.sv` - Real-world complex scenario

## Expected Test Results

Each test file is designed to validate specific DataFlowAnalyzer functionality:

1. **Graph Construction**: All signals correctly identified as nodes
2. **Edge Extraction**: All assignments correctly identified as edges
3. **Driver Analysis**: Correct identification of signal drivers
4. **Reader Analysis**: Correct identification of signal readers
5. **Fanout Calculation**: Accurate fanout computation
6. **Multi-Driver Detection**: Correct conflict identification
7. **Dependency Chains**: Accurate transitive closure
8. **Constant Propagation**: Correct constant identification

## Test Data Characteristics

- **Simple Cases**: Clear, unambiguous data flow
- **Edge Cases**: Empty modules, unconnected signals
- **Error Cases**: Multi-driver conflicts, circular dependencies
- **Integration Cases**: Cross-module data flow
- **Real-World Cases**: Complex, realistic SystemVerilog patterns

