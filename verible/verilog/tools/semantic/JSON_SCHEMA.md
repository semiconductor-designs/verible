# JSON Schema Documentation

**Version**: 1.0.0  
**Last Updated**: October 18, 2025  
**Tool**: verible-verilog-semantic

---

## Overview

This document describes the JSON schema for the `verible-verilog-semantic` tool output. The tool exports semantic analysis results (call graphs, data flow, unused entities) in JSON format for consumption by external tools.

### Schema Versioning

All JSON exports include a `schema_version` field at the root level to enable backward compatibility tracking.

```json
{
  "schema_version": "1.0.0",
  "call_graph": { ... },
  "data_flow": { ... },
  "unused": { ... }
}
```

### Stability Guarantees

- **Stable Fields**: Will not be removed or renamed in minor/patch versions
- **Experimental Fields**: May change in minor versions (marked below)
- **Deprecated Fields**: Will be supported for at least 2 major versions

---

## Schema Version: 1.0.0

### Root Level

| Field | Type | Status | Description |
|-------|------|--------|-------------|
| `schema_version` | string | **Stable** | Overall schema version (e.g., "1.0.0") |
| `call_graph` | object | **Stable** | Call graph analysis (optional, see below) |
| `data_flow` | object | **Stable** | Data flow analysis (optional, see below) |
| `unused` | object | **Stable** | Unused entity detection (optional, see below) |

**Note**: Top-level sections (`call_graph`, `data_flow`, `unused`) are only present if the corresponding analyzer was enabled via command-line flags.

---

## Call Graph Schema

### call_graph Object

| Field | Type | Status | Description |
|-------|------|--------|-------------|
| `version` | string | **Stable** | Call graph schema version |
| `nodes` | array | **Stable** | Array of function/task nodes |
| `edges` | array | **Stable** | Array of call relationships |
| `statistics` | object | **Stable** | Summary statistics |
| `recursion_cycles` | array | **Stable** | Detected recursion cycles |

### call_graph.nodes[] Object

| Field | Type | Status | Description |
|-------|------|--------|-------------|
| `name` | string | **Stable** | Function or task name |
| `type` | string | **Stable** | "function" or "task" |
| `call_depth` | integer | **Stable** | Max path length to leaf nodes (0 = leaf) |
| `is_entry_point` | boolean | **Stable** | True if no callers and has callees |
| `is_recursive` | boolean | **Stable** | True if part of recursion cycle |
| `is_unreachable` | boolean | **Stable** | True if no callers and no callees |
| `caller_count` | integer | **Stable** | Number of functions that call this |
| `callee_count` | integer | **Stable** | Number of functions this calls |

### call_graph.edges[] Object

| Field | Type | Status | Description |
|-------|------|--------|-------------|
| `caller` | string | **Stable** | Name of calling function/task |
| `callee` | string | **Stable** | Name of called function/task |

### call_graph.statistics Object

| Field | Type | Status | Description |
|-------|------|--------|-------------|
| `total_functions` | integer | **Stable** | Total number of functions |
| `total_tasks` | integer | **Stable** | Total number of tasks |
| `entry_points` | integer | **Stable** | Number of entry point functions |
| `unreachable_functions` | integer | **Stable** | Number of unreachable functions |
| `recursive_functions` | integer | **Stable** | Number of recursive functions |
| `max_call_depth` | integer | **Stable** | Maximum call depth in graph |

### call_graph.recursion_cycles[] Object

| Field | Type | Status | Description |
|-------|------|--------|-------------|
| `cycle` | array<string> | **Stable** | Ordered list of function names in cycle |

### Example: Call Graph

```json
{
  "schema_version": "1.0.0",
  "call_graph": {
    "version": "1.0.0",
    "nodes": [
      {
        "name": "add",
        "type": "function",
        "call_depth": 0,
        "is_entry_point": false,
        "is_recursive": false,
        "is_unreachable": false,
        "caller_count": 1,
        "callee_count": 0
      },
      {
        "name": "main",
        "type": "function",
        "call_depth": 1,
        "is_entry_point": true,
        "is_recursive": false,
        "is_unreachable": false,
        "caller_count": 0,
        "callee_count": 1
      }
    ],
    "edges": [
      {
        "caller": "main",
        "callee": "add"
      }
    ],
    "statistics": {
      "total_functions": 2,
      "total_tasks": 0,
      "entry_points": 1,
      "unreachable_functions": 0,
      "recursive_functions": 0,
      "max_call_depth": 1
    },
    "recursion_cycles": []
  }
}
```

---

## Data Flow Schema

### data_flow Object

| Field | Type | Status | Description |
|-------|------|--------|-------------|
| `version` | string | **Stable** | Data flow schema version |
| `nodes` | array | **Stable** | Array of signals/variables/ports/parameters |
| `edges` | array | **Stable** | Array of data dependencies |
| `parameters` | array | **Stable** | Array of parameters |
| `constant_list` | array<string> | **Stable** | List of constant names |

### data_flow.nodes[] Object

| Field | Type | Status | Description |
|-------|------|--------|-------------|
| `name` | string | **Stable** | Full hierarchical name |
| `local_name` | string | **Stable** | Local name within scope |
| `type` | string | **Stable** | "signal", "variable", "port", "parameter", or "constant" |
| `is_constant` | boolean | **Stable** | True if compile-time constant |
| `is_parameter` | boolean | **Stable** | True if parameter or localparam |
| `is_port` | boolean | **Stable** | True if module port |
| `is_read` | boolean | **Stable** | True if ever read from |
| `is_written` | boolean | **Stable** | True if ever written to |
| `has_multi_driver` | boolean | **Stable** | True if multiple drivers |
| `fanout` | integer | **Stable** | Number of readers |
| `driver_count` | integer | **Stable** | Number of drivers |

### data_flow.edges[] Object

| Field | Type | Status | Description |
|-------|------|--------|-------------|
| `source` | string | **Stable** | Source node name (driver) |
| `target` | string | **Stable** | Target node name (driven) |
| `type` | string | **Stable** | Edge type (see below) |
| `is_conditional` | boolean | **Stable** | True if inside if/case |

**Edge Types**:
- `"blocking"`: Blocking assignment (=)
- `"non_blocking"`: Non-blocking assignment (<=)
- `"continuous"`: Continuous assignment (assign)
- `"port_connection"`: Module port connection
- `"function_return"`: Function return value
- `"function_arg"`: Function argument

### data_flow.parameters[] Object

| Field | Type | Status | Description |
|-------|------|--------|-------------|
| `name` | string | **Stable** | Parameter name |
| `is_constant` | boolean | **Stable** | True (parameters are always constant) |

### Example: Data Flow

```json
{
  "schema_version": "1.0.0",
  "data_flow": {
    "version": "1.0.0",
    "nodes": [
      {
        "name": "m.WIDTH",
        "local_name": "WIDTH",
        "type": "parameter",
        "is_constant": true,
        "is_parameter": true,
        "is_port": false,
        "is_read": true,
        "is_written": false,
        "has_multi_driver": false,
        "fanout": 2,
        "driver_count": 0
      },
      {
        "name": "m.data",
        "local_name": "data",
        "type": "signal",
        "is_constant": false,
        "is_parameter": false,
        "is_port": false,
        "is_read": true,
        "is_written": true,
        "has_multi_driver": false,
        "fanout": 1,
        "driver_count": 1
      }
    ],
    "edges": [
      {
        "source": "m.clk",
        "target": "m.data",
        "type": "non_blocking",
        "is_conditional": false
      }
    ],
    "parameters": [
      {
        "name": "m.WIDTH",
        "is_constant": true
      }
    ],
    "constant_list": ["WIDTH", "DEPTH"]
  }
}
```

---

## Unused Entities Schema

### unused Object

| Field | Type | Status | Description |
|-------|------|--------|-------------|
| `version` | string | **Stable** | Unused detection schema version |
| `entities` | array | **Stable** | Array of unused entities |
| `statistics` | object | **Stable** | Summary statistics |
| `summary` | string | **Stable** | Human-readable summary |

### unused.entities[] Object

| Field | Type | Status | Description |
|-------|------|--------|-------------|
| `name` | string | **Stable** | Entity name |
| `type` | string | **Stable** | Entity type (see below) |
| `fully_qualified_name` | string | **Stable** | Full hierarchical name |

**Entity Types**:
- `"signal"`: Wire, reg, logic
- `"variable"`: Local variable
- `"function"`: Function
- `"task"`: Task
- `"module"`: Module definition
- `"port"`: Module port
- `"parameter"`: Parameter
- `"dead_code"`: Unreachable code block

### unused.statistics Object

| Field | Type | Status | Description |
|-------|------|--------|-------------|
| `total_signals` | integer | **Stable** | Total number of signals |
| `unused_signals` | integer | **Stable** | Number of unused signals |
| `total_variables` | integer | **Stable** | Total number of variables |
| `unused_variables` | integer | **Stable** | Number of unused variables |
| `total_functions` | integer | **Stable** | Total number of functions |
| `unused_functions` | integer | **Stable** | Number of unused functions |
| `total_modules` | integer | **Stable** | Total number of modules |
| `unused_modules` | integer | **Stable** | Number of unused modules |

### Example: Unused Entities

```json
{
  "schema_version": "1.0.0",
  "unused": {
    "version": "1.0.0",
    "entities": [
      {
        "name": "unused_signal",
        "type": "signal",
        "fully_qualified_name": "top.sub.unused_signal"
      },
      {
        "name": "dead_function",
        "type": "function",
        "fully_qualified_name": "top.dead_function"
      }
    ],
    "statistics": {
      "total_signals": 10,
      "unused_signals": 1,
      "total_variables": 5,
      "unused_variables": 0,
      "total_functions": 3,
      "unused_functions": 1,
      "total_modules": 2,
      "unused_modules": 0
    },
    "summary": "2 unused entities detected"
  }
}
```

---

## Backward Compatibility Policy

### Version Numbering

We follow [Semantic Versioning](https://semver.org/) for the schema:

- **Major version** (X.0.0): Breaking changes
  - Removing fields
  - Renaming fields
  - Changing field types
  - Changing field semantics

- **Minor version** (1.X.0): Backward-compatible additions
  - Adding new optional fields
  - Adding new sections
  - Adding new values to enums

- **Patch version** (1.0.X): Bug fixes
  - Fixing incorrect data
  - Improving documentation
  - Performance improvements

### Migration Guide

When the schema version changes, this section will document migration steps.

**Current Version**: 1.0.0 (initial release)

---

## Integration Best Practices

### Parsing Recommendations

**Lenient Parsing** (Recommended):
```python
data = json.loads(output)
schema_version = data.get("schema_version", "unknown")

# Tolerate missing fields
call_graph = data.get("call_graph", {})
nodes = call_graph.get("nodes", [])

for node in nodes:
    name = node.get("name", "")
    # Handle missing fields gracefully
```

**Strict Parsing** (For validation):
```python
data = json.loads(output)
assert data["schema_version"] == "1.0.0", "Incompatible schema version"
assert "call_graph" in data, "Missing call_graph"
# ... strict validation ...
```

### Handling Schema Version Changes

```python
def parse_verible_output(json_str):
    data = json.loads(json_str)
    version = data.get("schema_version", "1.0.0")
    
    major, minor, patch = map(int, version.split("."))
    
    if major > 1:
        logging.warning(f"Schema version {version} may be incompatible")
    
    # Parse based on version
    if major == 1:
        return parse_v1(data)
    else:
        raise ValueError(f"Unsupported schema version: {version}")
```

### Error Handling

Always check for parse errors:
```python
try:
    data = json.loads(output)
except json.JSONDecodeError as e:
    logging.error(f"Invalid JSON: {e}")
    # Handle error
```

### Performance Tips

1. **Selective Analysis**: Only request needed analyzers
   ```bash
   # Only call graph (faster)
   verible-verilog-semantic design.sv
   
   # All analyzers (slower but complete)
   verible-verilog-semantic --include_all design.sv
   ```

2. **Stream Processing**: For large outputs, consider streaming JSON parsing

3. **Caching**: Cache results for unchanged files

---

## Deprecation Policy

### Announcing Deprecations

Deprecated fields will be:
1. Marked in documentation (this file)
2. Retained for at least 2 major versions
3. Accompanied by migration guide

### Example Deprecation Notice

```
Field: old_field_name (DEPRECATED)
Status: Deprecated in v1.5.0, will be removed in v3.0.0
Replacement: Use new_field_name instead
Migration: Simply rename the field in your code
```

---

## Version History

### 1.0.0 (October 18, 2025)

- Initial release
- Call graph analysis
- Data flow analysis
- Unused entity detection
- Schema versioning support

---

## Contact & Support

For questions, issues, or feature requests:
- GitHub: https://github.com/chipsalliance/verible
- Issues: https://github.com/chipsalliance/verible/issues

---

**End of JSON Schema Documentation**

