# Interface Test Data

Test data for InterfaceValidator component.

## Directory Structure

```
interfaces/
├── basic/           - Basic interface tests
├── modport/         - Modport validation tests
├── connections/     - Interface connection tests
├── advanced/        - Advanced features (arrays, generics)
└── errors/          - Error case tests
```

## Test Categories

### Basic Tests (basic/)

1. **simple_interface.sv**
   - Simple interface with signals
   - Two modules communicating via interface
   - Tests basic interface instantiation and usage

2. **empty_interface.sv**
   - Edge case: empty interface with no signals
   - Tests minimal valid interface

3. **interface_with_params.sv**
   - Parameterized interface
   - Parameter overrides in instantiation
   - Tests parameter integration with interfaces

### Modport Tests (modport/)

4. **basic_modport.sv**
   - Master/slave modports
   - Input/output direction specification
   - Tests bidirectional communication

5. **multiple_modports.sv**
   - Multiple modports in one interface (cpu, memory, monitor)
   - Different views for different modules
   - Tests complex modport scenarios

6. **inout_modport.sv**
   - Bidirectional (inout) signals in modports
   - Tests tristate/bidirectional signal handling

### Connection Tests (connections/)

7. **direct_connection.sv**
   - Direct interface connection between modules
   - Tests simple interface passing

8. **hierarchical_connection.sv**
   - Interface passing through hierarchy
   - Tests interface propagation

### Advanced Tests (advanced/)

9. **interface_array.sv**
   - Array of interface instances
   - Tests generate loops with interfaces

10. **generic_interface.sv**
    - Parameterized type in interface
    - Type parameters
    - Tests advanced type parameterization

### Error Tests (errors/)

11. **wrong_modport.sv**
    - ERROR: Using modport with wrong direction
    - Writing to input-only modport
    - Reading from output without input

12. **missing_modport.sv**
    - ERROR: Referencing non-existent modport
    - Tests error detection

## Test Expectations

### Valid Cases (Tests 1-10)
- Should parse without errors
- Interface definitions should be extracted
- Modports should be validated
- Connections should be verified

### Error Cases (Tests 11-12)
- Should detect and report errors
- Invalid modport usage should fail
- Missing modport references should fail

## Usage

These test files are used by `interface-validator_test.cc` to verify:
1. Interface definition extraction
2. Modport parsing and validation
3. Interface connection checking
4. Signal direction validation
5. Error detection and reporting

## Coverage

- ✅ Basic interface declarations
- ✅ Modport definitions (input/output/inout)
- ✅ Interface instantiation
- ✅ Interface connections
- ✅ Parameterized interfaces
- ✅ Interface arrays
- ✅ Hierarchical connections
- ✅ Error cases

Total: 12 test files covering all major interface features.

