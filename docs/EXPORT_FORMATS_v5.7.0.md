# Verible v5.7.0 - JSON Export Formats Guide

**Version**: 1.0  
**Date**: October 20, 2025  
**Verible Version**: v5.7.0+

---

## Overview

Verible v5.7.0 introduces two JSON export formats for SystemVerilog analysis:

1. **Standard JSON Export** (`--export_json`) - v5.6.0 compatible format
2. **Indexed JSON Export** (`--export_indexed_json`) - v5.7.0 new format with file tracking

Both formats are fully supported and maintained. Choose based on your use case.

---

## Standard JSON Export (`--export_json`)

### Description

The standard format outputs one CST per file, with files as top-level keys. This format has been available since early Verible versions and is fully backward compatible.

### When to Use

- ✅ Single file analysis
- ✅ Existing tools that parse v5.6.0 output
- ✅ Simple workflows without multi-file tracking
- ✅ Backward compatibility required

### Command

```bash
verible-verilog-syntax --export_json file.sv
```

### Output Format

```json
{
  "verible_version": "v5.7.0-3940-ga1b2c3d4",
  "cst_schema_version": "1.0",
  "export_format": "standard",
  "timestamp": "2025-10-20T14:30:00Z",
  "file.sv": {
    "tree": {
      "tag": "kDescriptionList",
      "children": [...]
    }
  }
}
```

### Key Features

- **Flat structure**: Each file is a top-level JSON key
- **Direct CST access**: `json["file.sv"]["tree"]` gives CST immediately
- **File paths as keys**: Use filename string as JSON key
- **Backward compatible**: Identical structure to v5.6.0 (with added metadata)

### Multi-File Example

```bash
verible-verilog-syntax --export_json file1.sv file2.sv file3.sv
```

**Output**:

```json
{
  "verible_version": "v5.7.0-...",
  "cst_schema_version": "1.0",
  "export_format": "standard",
  "timestamp": "2025-10-20T14:30:00Z",
  "file1.sv": {
    "tree": {...}
  },
  "file2.sv": {
    "tree": {...}
  },
  "file3.sv": {
    "tree": {...}
  }
}
```

---

## Indexed JSON Export (`--export_indexed_json`)

### Description

The indexed format adds explicit file index mapping for large-scale batch processing. It resolves `<indexed>` placeholders to actual file paths and provides a structured format for multi-file workflows.

### When to Use

- ✅ Large batch processing (100+ files)
- ✅ Need to resolve `<indexed>` placeholders in CST nodes
- ✅ Multi-variant projects (e.g., OpenTitan with 4 chip variants)
- ✅ Tools that need explicit file-to-index mapping
- ✅ Production pipelines with file traceability requirements

### Command

```bash
verible-verilog-syntax --export_indexed_json file1.sv file2.sv file3.sv
```

### Output Format

```json
{
  "verible_version": "v5.7.0-3940-ga1b2c3d4",
  "cst_schema_version": "1.0",
  "export_format": "indexed",
  "timestamp": "2025-10-20T14:30:00Z",
  "file_index": {
    "0": "/absolute/path/to/file1.sv",
    "1": "/absolute/path/to/file2.sv",
    "2": "/absolute/path/to/file3.sv"
  },
  "cst": {
    "file1.sv": {
      "tree": {
        "tag": "kDescriptionList",
        "file": "<indexed>:0",
        "children": [...]
      }
    },
    "file2.sv": {
      "tree": {
        "file": "<indexed>:1",
        ...
      }
    },
    "file3.sv": {
      "tree": {
        "file": "<indexed>:2",
        ...
      }
    }
  }
}
```

### Key Features

- **File index mapping**: `file_index` maps string indices to absolute paths
- **Indexed placeholders**: CST nodes use `<indexed>:N` format
- **Structured hierarchy**: CSTs wrapped under `"cst"` key
- **Path normalization**: All paths converted to absolute for consistency
- **Deduplication**: Same file added multiple times gets same index

### Resolving `<indexed>` Placeholders

When you see `"file": "<indexed>:0"` in a CST node:

1. Extract the index: `"0"`
2. Look up in `file_index`: `file_index["0"]`
3. Result: `/absolute/path/to/file1.sv`

**Example code** (Python):

```python
import json

with open('output.json') as f:
    data = json.load(f)

# Resolve indexed file reference
file_index = data['file_index']
for filename, file_data in data['cst'].items():
    node_file_ref = file_data['tree']['file']  # "<indexed>:0"
    
    if node_file_ref.startswith('<indexed>:'):
        index_id = node_file_ref.split(':')[1]  # "0"
        actual_path = file_index[index_id]       # "/absolute/path/..."
        print(f"{filename} -> {actual_path}")
```

---

## Version Metadata (Both Formats)

### Fields

Both export formats include top-level metadata:

| Field | Type | Description | Example |
|-------|------|-------------|---------|
| `verible_version` | string | Verible build version | `"v5.7.0-3940-ga1b2c3d4"` |
| `cst_schema_version` | string | CST schema version | `"1.0"` |
| `export_format` | string | Format type | `"standard"` or `"indexed"` |
| `timestamp` | string | ISO 8601 timestamp (UTC) | `"2025-10-20T14:30:00Z"` |

### Purpose

- **Version compatibility checking**: Verify tool compatibility before parsing
- **Schema evolution tracking**: Detect CST structure changes
- **Audit trail**: Track when analysis was performed
- **Format detection**: Programmatically identify export format

### Checking Compatibility

**Example** (Python):

```python
import json

def validate_version(json_path):
    with open(json_path) as f:
        data = json.load(f)
    
    # Check schema version
    schema_version = data.get('cst_schema_version')
    if schema_version != '1.0':
        raise ValueError(f"Incompatible schema version: {schema_version}")
    
    # Check format type
    export_format = data.get('export_format')
    print(f"Detected format: {export_format}")
    
    return data

# Usage
data = validate_version('output.json')
```

---

## Comparison Table

| Feature | Standard (`--export_json`) | Indexed (`--export_indexed_json`) |
|---------|---------------------------|----------------------------------|
| **Backward compatible** | ✅ v5.6.0+ | ⚠️ New in v5.7.0 |
| **File index mapping** | ❌ No | ✅ Yes |
| **CST structure** | Flat (top-level files) | Nested (under `"cst"`) |
| **File references** | Direct paths | `<indexed>:N` format |
| **Path normalization** | As provided | Absolute paths |
| **Batch processing** | ✅ Supported | ✅ Optimized |
| **Large-scale (1000+ files)** | ⚠️ Works but no tracking | ✅ Designed for this |
| **Version metadata** | ✅ Yes | ✅ Yes |

---

## Use Case Examples

### Use Case 1: Single File Analysis

**Goal**: Parse one file, get CST

**Recommended**: `--export_json` (simpler structure)

```bash
verible-verilog-syntax --export_json module.sv > output.json
```

**Access CST**:

```python
cst = json_data["module.sv"]["tree"]
```

---

### Use Case 2: Small Batch (< 100 files)

**Goal**: Parse 50 files, simple workflow

**Recommended**: `--export_json` (backward compatible)

```bash
verible-verilog-syntax --export_json *.sv > output.json
```

**Iterate files**:

```python
for filename, file_data in json_data.items():
    if filename not in ['verible_version', 'cst_schema_version', 
                        'export_format', 'timestamp']:
        cst = file_data['tree']
        process_cst(cst)
```

---

### Use Case 3: Large Batch (OpenTitan: 3,659 files)

**Goal**: Parse entire OpenTitan repository with file tracking

**Recommended**: `--export_indexed_json` (explicit file mapping)

```bash
verible-verilog-syntax --export_indexed_json \
    --continue_on_error \
    $(find opentitan -name "*.sv") > output.json
```

**Process with traceability**:

```python
file_index = json_data['file_index']

for filename, file_data in json_data['cst'].items():
    cst = file_data['tree']
    
    # Resolve any <indexed>:N references in CST
    for node in traverse_cst(cst):
        if 'file' in node and node['file'].startswith('<indexed>:'):
            index_id = node['file'].split(':')[1]
            node['resolved_file'] = file_index[index_id]
```

---

### Use Case 4: Multi-Variant Projects

**Goal**: Parse OpenTitan variants (earlgrey, englishbreakfast, darjeeling, teacup)

**Recommended**: `--export_indexed_json` (deduplication + tracking)

```bash
# Process all variants
for variant in earlgrey englishbreakfast darjeeling teacup; do
    verible-verilog-syntax --export_indexed_json \
        hw/top_${variant}/rtl/*.sv > ${variant}.json
done
```

**Benefit**: File index prevents duplicate path confusion across variants.

---

## Migration Guide (v5.6.0 → v5.7.0)

### If Using `--export_json`

**No changes required!** ✅

Your existing code will work identically. The only addition is top-level metadata:

**Before (v5.6.0)**:

```json
{
  "file.sv": {"tree": {...}}
}
```

**After (v5.7.0)**:

```json
{
  "verible_version": "v5.7.0-...",
  "cst_schema_version": "1.0",
  "export_format": "standard",
  "timestamp": "2025-10-20T14:30:00Z",
  "file.sv": {"tree": {...}}
}
```

**Update your parser** (optional but recommended):

```python
# Old code (still works)
for filename, file_data in json_data.items():
    cst = file_data['tree']

# New code (filter metadata)
METADATA_KEYS = {'verible_version', 'cst_schema_version', 
                 'export_format', 'timestamp'}

for filename, file_data in json_data.items():
    if filename not in METADATA_KEYS:
        cst = file_data['tree']
```

---

### If Upgrading to `--export_indexed_json`

**Migration steps**:

1. **Change flag**: `--export_json` → `--export_indexed_json`

2. **Update JSON parsing**:

   ```python
   # Old (v5.6.0 with --export_json)
   for filename, file_data in json_data.items():
       cst = file_data['tree']
   
   # New (v5.7.0 with --export_indexed_json)
   file_index = json_data['file_index']
   for filename, file_data in json_data['cst'].items():
       cst = file_data['tree']
   ```

3. **Add file index resolution** (if needed):

   ```python
   def resolve_indexed_ref(ref, file_index):
       if ref.startswith('<indexed>:'):
           index_id = ref.split(':')[1]
           return file_index[index_id]
       return ref
   ```

4. **Validate schema version**:

   ```python
   assert json_data['cst_schema_version'] == '1.0'
   ```

---

## Error Handling (v5.7.0)

### With `--continue_on_error`

Both export formats support error recovery:

```bash
verible-verilog-syntax --export_indexed_json --continue_on_error *.sv
```

**Output includes status**:

```json
{
  "file_index": {...},
  "cst": {
    "good_file.sv": {
      "status": "success",
      "tree": {...}
    },
    "bad_file.sv": {
      "status": "partial",
      "error": {
        "message": "Syntax error at line 42",
        "line": 42,
        "column": 15,
        "context": "module foo(input x, output y);\n..."
      },
      "partial_cst": {...}
    }
  }
}
```

**Status values**:

- `"success"` - File parsed completely
- `"partial"` - Parse error, but partial CST available
- `"failed"` - Parse error, no CST available

---

## Performance Considerations

### Memory Usage

- **Standard format**: Minimal overhead (~1% per file)
- **Indexed format**: Adds file index (~0.1 KB per file)

**Example**: 1,000 files with indexed JSON adds ~100 KB overhead.

### Processing Speed

- **Standard format**: Baseline (100%)
- **Indexed format**: +0.5% (path normalization overhead)

**Example**: Parsing 3,659 OpenTitan files takes ~45 seconds with either format.

### Recommendations

- **< 100 files**: Use either format (no measurable difference)
- **100-1000 files**: Use `--export_indexed_json` for better traceability
- **1000+ files**: **Strongly recommend** `--export_indexed_json`

---

## Best Practices

### 1. Always Check Schema Version

```python
def validate_schema(data):
    if data.get('cst_schema_version') != '1.0':
        raise ValueError("Incompatible CST schema")
```

### 2. Use Absolute Paths for Reproducibility

Indexed JSON normalizes to absolute paths automatically:

```bash
# Automatically converts to absolute
verible-verilog-syntax --export_indexed_json ../rtl/module.sv
```

### 3. Enable Continue-on-Error for Large Repos

```bash
# Don't let one bad file block 3,658 others
verible-verilog-syntax --export_indexed_json --continue_on_error $(find . -name "*.sv")
```

### 4. Cache File Index for Repeated Lookups

```python
class VerilogAnalyzer:
    def __init__(self, json_path):
        with open(json_path) as f:
            data = json.load(f)
        
        self.file_index = data.get('file_index', {})
        self.csts = data.get('cst', data)  # Handle both formats
    
    def resolve_file(self, ref):
        if ref.startswith('<indexed>:'):
            return self.file_index[ref.split(':')[1]]
        return ref
```

---

## Troubleshooting

### Issue: "Error: --export_json and --export_indexed_json are mutually exclusive"

**Cause**: Both flags specified

**Solution**: Use only one:

```bash
# WRONG
verible-verilog-syntax --export_json --export_indexed_json file.sv

# CORRECT
verible-verilog-syntax --export_indexed_json file.sv
```

---

### Issue: "KeyError: 'file_index'"

**Cause**: Using `--export_json` but code expects `--export_indexed_json` format

**Solution**: Check `export_format` field:

```python
export_format = data.get('export_format', 'standard')

if export_format == 'indexed':
    file_index = data['file_index']
    csts = data['cst']
else:
    file_index = None
    csts = {k: v for k, v in data.items() 
            if k not in METADATA_KEYS}
```

---

### Issue: Cannot resolve `<indexed>:N` reference

**Cause**: Missing file index

**Solution**: Ensure using `--export_indexed_json`:

```python
if 'file_index' not in data:
    raise ValueError("File index not found. Use --export_indexed_json")
```

---

## Examples by Language

### Python

```python
import json

def parse_verible_output(json_path):
    with open(json_path) as f:
        data = json.load(f)
    
    # Validate version
    assert data['cst_schema_version'] == '1.0'
    
    # Detect format
    if data['export_format'] == 'indexed':
        return parse_indexed(data)
    else:
        return parse_standard(data)

def parse_indexed(data):
    file_index = data['file_index']
    results = {}
    
    for filename, file_data in data['cst'].items():
        if file_data.get('status') == 'success':
            results[filename] = file_data['tree']
    
    return results, file_index

def parse_standard(data):
    METADATA = {'verible_version', 'cst_schema_version', 
                'export_format', 'timestamp'}
    
    results = {}
    for filename, file_data in data.items():
        if filename not in METADATA:
            results[filename] = file_data['tree']
    
    return results, None
```

---

### JavaScript / Node.js

```javascript
const fs = require('fs');

function parseVeribleOutput(jsonPath) {
    const data = JSON.parse(fs.readFileSync(jsonPath, 'utf8'));
    
    // Validate schema
    if (data.cst_schema_version !== '1.0') {
        throw new Error('Incompatible CST schema');
    }
    
    // Handle format
    if (data.export_format === 'indexed') {
        return parseIndexed(data);
    } else {
        return parseStandard(data);
    }
}

function parseIndexed(data) {
    const fileIndex = data.file_index;
    const results = {};
    
    for (const [filename, fileData] of Object.entries(data.cst)) {
        if (fileData.status === 'success') {
            results[filename] = fileData.tree;
        }
    }
    
    return { results, fileIndex };
}

function parseStandard(data) {
    const METADATA = new Set([
        'verible_version', 'cst_schema_version', 
        'export_format', 'timestamp'
    ]);
    
    const results = {};
    for (const [filename, fileData] of Object.entries(data)) {
        if (!METADATA.has(filename)) {
            results[filename] = fileData.tree;
        }
    }
    
    return { results, fileIndex: null };
}
```

---

## FAQ

### Q: Which format should I use?

**A**: 
- Small projects (< 100 files): Either format works
- Large projects (100+ files): Use `--export_indexed_json`
- Existing tools: Keep `--export_json` (backward compatible)
- New tools: Prefer `--export_indexed_json` (future-proof)

### Q: Will `--export_json` be deprecated?

**A**: No! Standard JSON export is a core feature and will be maintained indefinitely. Both formats are first-class citizens.

### Q: Can I convert between formats?

**A**: Yes, you can convert indexed → standard programmatically:

```python
def indexed_to_standard(indexed_data):
    standard = {
        'verible_version': indexed_data['verible_version'],
        'cst_schema_version': indexed_data['cst_schema_version'],
        'export_format': 'standard',
        'timestamp': indexed_data['timestamp']
    }
    
    # Flatten CSTs to top level
    for filename, file_data in indexed_data['cst'].items():
        standard[filename] = file_data
    
    return standard
```

### Q: What happens to `cst_schema_version` if CST format changes?

**A**: Version will increment (`"1.0"` → `"2.0"`). Verible commits to:
- **Deprecation warnings** (2 releases before breaking change)
- **Migration guide** (old → new structure)
- **Backward compatibility** (2 releases support both versions)

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | Oct 20, 2025 | Initial v5.7.0 release |

---

## Related Documentation

- `V5.7.0_RELEASE_NOTES.md` - Full release notes
- `V5.7.0_MIGRATION_GUIDE.md` - Detailed migration instructions
- `docs/ERROR_RECOVERY_GUIDE.md` - Error handling with `--continue_on_error`
- `docs/CST_SCHEMA_v1.0.md` - Complete CST schema reference

---

**Questions?** Open an issue on GitHub: https://github.com/chipsalliance/verible/issues

