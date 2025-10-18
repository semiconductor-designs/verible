# Verible Semantic Analysis Tool - Design Document

**Tool Name**: `verible-verilog-semantic`  
**Purpose**: Export Verible's semantic analysis as JSON for external tools (VeriPG, etc.)  
**Status**: Design Phase  
**Target Date**: Week of October 21, 2025

---

## Executive Summary

Create a new Verible tool that exports the complete semantic analysis of SystemVerilog code as structured JSON. This enables external tools (like VeriPG) to leverage Verible's 100% tested semantic framework without reimplementation.

**Key Benefits**:
- Expose Verible's CallGraphEnhancer, DataFlowAnalyzer, EnhancedUnusedDetector
- 2-4x speedup for downstream tools
- Enable cross-file semantic analysis
- Production-quality semantic information (71/71 tests)

---

## Tool Architecture

### Command-Line Interface

```bash
verible-verilog-semantic [OPTIONS] FILES...

Options:
  --output-format <json|jsonl|proto>     Output format (default: json)
  --output-file <path>                   Output file (default: stdout)
  --include-ast                          Include AST structure
  --include-semantic                     Include semantic analysis (default)
  --include-callgraph                    Include function call graph
  --include-dataflow                     Include data flow analysis
  --include-unused                       Include unused entity detection
  --include-hierarchy                    Include module hierarchy
  --include-all                          Include everything
  --project-root <path>                  Multi-file project root
  --cache-dir <path>                     Enable caching (for performance)
  --pretty                               Pretty-print JSON output

Examples:
  # Basic semantic analysis
  verible-verilog-semantic design.sv

  # Call graph only
  verible-verilog-semantic --include-callgraph design.sv

  # Complete analysis with caching
  verible-verilog-semantic --include-all --cache-dir .cache design.sv

  # Multi-file project
  verible-verilog-semantic --project-root . top.sv sub.sv pkg.sv
```

---

## Output Schema

### Top-Level Structure

```json
{
  "version": "5.1.0",
  "tool": "verible-verilog-semantic",
  "timestamp": "2025-10-18T20:00:00Z",
  "files": [
    {
      "path": "design.sv",
      "hash": "md5:abc123...",
      "modules": [...],
      "semantic": {...},
      "call_graph": {...},
      "data_flow": {...},
      "unused": {...}
    }
  ],
  "project": {
    "hierarchy": {...},
    "cross_references": [...]
  }
}
```

---

### Module Information

```json
{
  "modules": [
    {
      "name": "counter",
      "file": "design.sv",
      "line": 10,
      "type": "module",
      "ports": [
        {
          "name": "clk",
          "direction": "input",
          "type": {
            "base": "logic",
            "width": 1,
            "packed_dims": [],
            "unpacked_dims": [],
            "signed": false
          },
          "line": 11
        },
        {
          "name": "data",
          "direction": "output",
          "type": {
            "base": "logic",
            "width": 8,
            "packed_dims": [{"left": 7, "right": 0}],
            "unpacked_dims": [],
            "signed": false
          },
          "line": 13
        }
      ],
      "parameters": [
        {
          "name": "WIDTH",
          "type": "localparam",
          "value": "8",
          "is_constant": true,
          "line": 15
        }
      ],
      "signals": [
        {
          "name": "count_reg",
          "type": {
            "base": "logic",
            "width": 8,
            "packed_dims": [{"left": 7, "right": 0}],
            "unpacked_dims": [],
            "signed": false
          },
          "is_register": true,
          "is_wire": false,
          "line": 17
        }
      ],
      "instances": [
        {
          "name": "u_sub",
          "module_type": "sub_counter",
          "line": 20,
          "port_connections": [
            {"port": "clk", "net": "clk"},
            {"port": "data", "net": "count_reg"}
          ]
        }
      ],
      "functions": [
        {
          "name": "increment",
          "return_type": {
            "base": "logic",
            "width": 8,
            "packed_dims": [{"left": 7, "right": 0}]
          },
          "parameters": [
            {"name": "val", "type": {"base": "logic", "width": 8}}
          ],
          "line": 25
        }
      ]
    }
  ]
}
```

---

### Call Graph (from CallGraphEnhancer)

```json
{
  "call_graph": {
    "nodes": [
      {
        "name": "top_level",
        "type": "function",
        "file": "design.sv",
        "line": 30,
        "call_depth": 2,
        "is_entry_point": true,
        "is_recursive": false,
        "is_unreachable": false,
        "caller_count": 0,
        "callee_count": 2
      },
      {
        "name": "helper",
        "type": "task",
        "file": "design.sv",
        "line": 40,
        "call_depth": 1,
        "is_entry_point": false,
        "is_recursive": false,
        "is_unreachable": false,
        "caller_count": 2,
        "callee_count": 1
      }
    ],
    "edges": [
      {
        "caller": "top_level",
        "callee": "helper",
        "call_site_line": 35
      },
      {
        "caller": "helper",
        "callee": "leaf_function",
        "call_site_line": 45
      }
    ],
    "statistics": {
      "total_functions": 10,
      "total_tasks": 3,
      "entry_points": 2,
      "unreachable": 1,
      "recursive": 0,
      "max_call_depth": 5
    },
    "recursion_cycles": []
  }
}
```

---

### Data Flow (from DataFlowAnalyzer)

```json
{
  "data_flow": {
    "nodes": [
      {
        "name": "clk",
        "qualified_name": "counter.clk",
        "type": "port",
        "is_input": true,
        "is_output": false,
        "is_parameter": false,
        "is_constant": false,
        "file": "design.sv",
        "line": 11
      },
      {
        "name": "count_reg",
        "qualified_name": "counter.count_reg",
        "type": "signal",
        "is_input": false,
        "is_output": false,
        "is_parameter": false,
        "is_constant": false,
        "file": "design.sv",
        "line": 17
      },
      {
        "name": "WIDTH",
        "qualified_name": "counter.WIDTH",
        "type": "parameter",
        "is_input": false,
        "is_output": false,
        "is_parameter": true,
        "is_constant": true,
        "value": "8",
        "file": "design.sv",
        "line": 15
      }
    ],
    "edges": [
      {
        "source": "clk",
        "target": "count_reg",
        "type": "clock",
        "description": "count_reg is clocked by clk"
      },
      {
        "source": "count_reg",
        "target": "data",
        "type": "assignment",
        "description": "count_reg drives data"
      }
    ],
    "parameters": [
      {
        "name": "WIDTH",
        "qualified_name": "counter.WIDTH",
        "value": "8",
        "is_constant": true
      }
    ],
    "constant_list": [
      {
        "name": "WIDTH",
        "value": "8"
      }
    ]
  }
}
```

---

### Unused Entities (from EnhancedUnusedDetector)

```json
{
  "unused": {
    "entities": [
      {
        "name": "debug_signal",
        "type": "signal",
        "reason": "Never read or written",
        "severity": "warning",
        "file": "design.sv",
        "line": 50,
        "suggestions": [
          "Remove if not needed",
          "Use for debugging",
          "Add to ignore patterns"
        ]
      },
      {
        "name": "old_function",
        "type": "function",
        "reason": "Never called",
        "severity": "info",
        "file": "design.sv",
        "line": 60,
        "suggestions": [
          "Remove dead code",
          "Mark as utility function"
        ]
      }
    ],
    "statistics": {
      "total_signals": 25,
      "unused_signals": 1,
      "total_variables": 10,
      "unused_variables": 0,
      "total_functions": 8,
      "unused_functions": 1,
      "total_modules": 3,
      "unused_modules": 0
    },
    "summary": "1 unused signal, 1 unused function detected"
  }
}
```

---

### Module Hierarchy

```json
{
  "project": {
    "hierarchy": {
      "root": "top",
      "modules": {
        "top": {
          "file": "top.sv",
          "line": 10,
          "children": [
            {
              "instance_name": "u_counter",
              "module_type": "counter",
              "file": "counter.sv"
            },
            {
              "instance_name": "u_fifo",
              "module_type": "fifo",
              "file": "fifo.sv"
            }
          ]
        },
        "counter": {
          "file": "counter.sv",
          "line": 5,
          "children": []
        },
        "fifo": {
          "file": "fifo.sv",
          "line": 8,
          "children": [
            {
              "instance_name": "u_memory",
              "module_type": "mem_block",
              "file": "mem.sv"
            }
          ]
        }
      }
    },
    "cross_references": [
      {
        "from": "top.u_counter",
        "to": "counter",
        "type": "instantiation",
        "file": "top.sv",
        "line": 15
      },
      {
        "from": "top.u_fifo",
        "to": "fifo",
        "type": "instantiation",
        "file": "top.sv",
        "line": 20
      }
    ],
    "dependencies": {
      "top": ["counter", "fifo"],
      "fifo": ["mem_block"],
      "counter": [],
      "mem_block": []
    }
  }
}
```

---

## Implementation Plan

### Phase 1: Core Infrastructure (Day 1-2)

**Task 1.1**: Create tool skeleton
```cpp
// verible/verilog/tools/semantic/verible-verilog-semantic.cc

#include "verible/verilog/analysis/call-graph-enhancer.h"
#include "verible/verilog/analysis/data-flow-analyzer.h"
#include "verible/verilog/analysis/enhanced-unused-detector.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/project/verilog-project.h"

int main(int argc, char** argv) {
  // Parse command line
  // Load files
  // Run analyses
  // Export JSON
}
```

**Task 1.2**: JSON serialization framework
```cpp
// verible/verilog/tools/semantic/json-exporter.h

class SemanticJsonExporter {
 public:
  std::string ExportCallGraph(const CallGraphEnhancer& cg);
  std::string ExportDataFlow(const DataFlowAnalyzer& df);
  std::string ExportUnused(const EnhancedUnusedDetector& unused);
  std::string ExportHierarchy(const SymbolTable& st);
  std::string ExportComplete(const SemanticAnalysisResult& result);
};
```

**Deliverables**:
- Tool skeleton with CLI parsing
- JSON exporter class structure
- Basic BUILD file

---

### Phase 2: Semantic Analysis Integration (Day 3-4)

**Task 2.1**: Integrate CallGraphEnhancer
```cpp
// Export call graph to JSON

std::string ExportCallGraph(const CallGraphEnhancer& cg) {
  nlohmann::json j;
  j["call_graph"]["nodes"] = nlohmann::json::array();
  
  for (const auto* node : cg.GetAllNodes()) {
    nlohmann::json node_json;
    node_json["name"] = node->name;
    node_json["call_depth"] = node->call_depth;
    node_json["is_entry_point"] = cg.IsEntryPoint(node);
    node_json["is_recursive"] = node->is_recursive;
    // ... more fields
    j["call_graph"]["nodes"].push_back(node_json);
  }
  
  // Export edges
  for (const auto* edge : cg.GetAllEdges()) {
    nlohmann::json edge_json;
    edge_json["caller"] = edge->caller->name;
    edge_json["callee"] = edge->callee->name;
    j["call_graph"]["edges"].push_back(edge_json);
  }
  
  return j.dump(2);  // Pretty print with 2-space indent
}
```

**Task 2.2**: Integrate DataFlowAnalyzer
```cpp
std::string ExportDataFlow(const DataFlowAnalyzer& df) {
  nlohmann::json j;
  const auto& graph = df.GetDataFlowGraph();
  
  // Export nodes
  for (const auto& node : graph.nodes) {
    nlohmann::json node_json;
    node_json["name"] = node.name;
    node_json["type"] = NodeTypeToString(node.type);
    node_json["is_parameter"] = node.is_parameter;
    node_json["is_constant"] = node.is_constant;
    j["data_flow"]["nodes"].push_back(node_json);
  }
  
  // Export edges
  for (const auto& edge : graph.edges) {
    nlohmann::json edge_json;
    edge_json["source"] = edge.source;
    edge_json["target"] = edge.target;
    edge_json["type"] = EdgeTypeToString(edge.type);
    j["data_flow"]["edges"].push_back(edge_json);
  }
  
  return j.dump(2);
}
```

**Task 2.3**: Integrate EnhancedUnusedDetector
```cpp
std::string ExportUnused(const EnhancedUnusedDetector& detector) {
  nlohmann::json j;
  
  for (const auto& entity : detector.GetUnusedEntities()) {
    nlohmann::json entity_json;
    entity_json["name"] = entity.name;
    entity_json["type"] = EntityTypeToString(entity.type);
    entity_json["file"] = entity.file;
    entity_json["line"] = entity.line;
    j["unused"]["entities"].push_back(entity_json);
  }
  
  // Statistics
  const auto& stats = detector.GetStatistics();
  j["unused"]["statistics"]["total_signals"] = stats.total_signals;
  j["unused"]["statistics"]["unused_signals"] = stats.unused_signals;
  
  return j.dump(2);
}
```

**Deliverables**:
- CallGraph JSON export
- DataFlow JSON export
- Unused entities JSON export
- Unit tests for each exporter

---

### Phase 3: Module Hierarchy (Day 5)

**Task 3.1**: Export SymbolTable hierarchy
```cpp
std::string ExportHierarchy(const SymbolTable& symbol_table) {
  nlohmann::json j;
  
  // Traverse symbol table
  const auto& root = symbol_table.Root();
  for (const auto& child : root.Children()) {
    if (child.Value().metatype == SymbolMetaType::kModule) {
      nlohmann::json module_json;
      module_json["name"] = std::string(*child.Key());
      
      // Extract ports, parameters, instances
      ExtractModuleInfo(child, module_json);
      
      j["modules"].push_back(module_json);
    }
  }
  
  return j.dump(2);
}
```

**Deliverables**:
- Module hierarchy export
- Cross-reference extraction
- Dependency graph

---

### Phase 4: Testing & Documentation (Day 6-7)

**Task 4.1**: Unit tests
```cpp
// verible/verilog/tools/semantic/verible-verilog-semantic_test.cc

TEST(SemanticJsonExporterTest, CallGraphExport) {
  // Setup
  const char* code = R"(
    function void caller();
      helper();
    endfunction
    
    function void helper();
    endfunction
  )";
  
  auto analyzer = AnalyzeCode(code);
  auto json_str = ExportCallGraph(analyzer.call_graph);
  
  // Parse JSON
  auto j = nlohmann::json::parse(json_str);
  
  // Verify
  EXPECT_EQ(j["call_graph"]["nodes"].size(), 2);
  EXPECT_EQ(j["call_graph"]["edges"].size(), 1);
  EXPECT_EQ(j["call_graph"]["edges"][0]["caller"], "caller");
  EXPECT_EQ(j["call_graph"]["edges"][0]["callee"], "helper");
}

TEST(SemanticJsonExporterTest, DataFlowExport) {
  // Similar tests for data flow
}

TEST(SemanticJsonExporterTest, UnusedExport) {
  // Similar tests for unused detection
}
```

**Task 4.2**: Integration tests
```bash
# Test with real SystemVerilog files
$ verible-verilog-semantic testdata/counter.sv > output.json
$ python3 -m json.tool output.json  # Validate JSON
$ jq '.call_graph.nodes | length' output.json  # Query
```

**Task 4.3**: Documentation
- README for the tool
- JSON schema documentation
- Usage examples
- Integration guide for VeriPG

**Deliverables**:
- 20+ unit tests
- Integration tests with real files
- Complete documentation

---

## BUILD Configuration

```python
# verible/verilog/tools/semantic/BUILD

cc_library(
    name = "json-exporter",
    srcs = ["json-exporter.cc"],
    hdrs = ["json-exporter.h"],
    deps = [
        "//verible/verilog/analysis:call-graph-enhancer",
        "//verible/verilog/analysis:data-flow-analyzer",
        "//verible/verilog/analysis:enhanced-unused-detector",
        "//verible/verilog/analysis:symbol-table",
        "@nlohmann_json//:json",
    ],
)

cc_binary(
    name = "verible-verilog-semantic",
    srcs = ["verible-verilog-semantic.cc"],
    deps = [
        ":json-exporter",
        "//verible/common/util:init-command-line",
        "//verible/verilog/project:verilog-project",
        "@abseil-cpp//absl/flags:flag",
        "@abseil-cpp//absl/status",
    ],
)

cc_test(
    name = "json-exporter_test",
    srcs = ["json-exporter_test.cc"],
    deps = [
        ":json-exporter",
        "@googletest//:gtest",
        "@googletest//:gtest_main",
    ],
)
```

---

## Dependencies

**External**:
- `nlohmann/json` for JSON serialization (if not already present)
  - Alternative: Abseil's JSON support
  - Alternative: Manual JSON string building

**Internal**:
- `call-graph-enhancer` (✅ complete, 33/33 tests)
- `data-flow-analyzer` (✅ complete, 17/17 tests)
- `enhanced-unused-detector` (✅ complete, 21/21 tests)
- `symbol-table` (✅ existing)
- `verilog-project` (✅ existing)

---

## Performance Considerations

### Memory

**Concern**: JSON output can be large for big projects

**Solution**:
- Streaming JSON output (JSONL format)
- Selective export (--include-callgraph only)
- Compression support (gzip output)

```bash
# Stream large projects
$ verible-verilog-semantic --output-format jsonl design.sv | gzip > output.jsonl.gz

# Selective export
$ verible-verilog-semantic --include-callgraph design.sv  # Only call graph
```

---

### Speed

**Concern**: Analysis may be slow for large files

**Solution**:
- Caching (--cache-dir)
- Incremental analysis
- Parallel file processing

```bash
# Enable caching
$ verible-verilog-semantic --cache-dir .cache design.sv

# First run: 1.5s (full analysis)
# Cached run: 0.1s (load from cache)
```

---

## VeriPG Integration Example

```python
# VeriPG v3.0: Use Verible semantic tool

import subprocess
import json

class VeribleSemanticExtractor:
    def __init__(self, verible_path="verible-verilog-semantic"):
        self.verible_path = verible_path
    
    def extract(self, sv_file, include_all=True):
        """Extract semantic information from SystemVerilog file."""
        cmd = [self.verible_path]
        if include_all:
            cmd.append("--include-all")
        cmd.append(sv_file)
        
        result = subprocess.run(cmd, capture_output=True, text=True)
        return json.loads(result.stdout)
    
    def get_call_graph(self, sv_file):
        """Get only call graph."""
        cmd = [self.verible_path, "--include-callgraph", sv_file]
        result = subprocess.run(cmd, capture_output=True, text=True)
        data = json.loads(result.stdout)
        return data["call_graph"]
    
    def get_unused_entities(self, sv_file):
        """Get unused entity detection."""
        cmd = [self.verible_path, "--include-unused", sv_file]
        result = subprocess.run(cmd, capture_output=True, text=True)
        data = json.loads(result.stdout)
        return data["unused"]["entities"]

# Usage in VeriPG
extractor = VeribleSemanticExtractor()
semantics = extractor.extract("design.sv")

# Use semantic data
for func in semantics["call_graph"]["nodes"]:
    if func["is_unreachable"]:
        print(f"Warning: Function {func['name']} is unreachable")

for entity in extractor.get_unused_entities("design.sv"):
    print(f"Unused {entity['type']}: {entity['name']} at line {entity['line']}")
```

---

## Success Criteria

### Functional
- ✅ Export all semantic analysis results
- ✅ Valid JSON output
- ✅ Complete information (no data loss)
- ✅ Handles multi-file projects

### Performance
- ✅ < 2s for typical module (1000 lines)
- ✅ < 10s for large module (10000 lines)
- ✅ < 1s with caching (unchanged files)

### Quality
- ✅ 20+ unit tests
- ✅ Integration tests with real files
- ✅ JSON schema validation
- ✅ Complete documentation

### Usability
- ✅ Clear CLI interface
- ✅ Good error messages
- ✅ Examples for common use cases
- ✅ Integration guide

---

## Timeline

| Day | Tasks | Deliverables |
|-----|-------|--------------|
| 1-2 | Core infrastructure | Tool skeleton, JSON framework |
| 3-4 | Semantic integration | CallGraph, DataFlow, Unused exports |
| 5 | Hierarchy | Module hierarchy, cross-references |
| 6-7 | Testing & docs | 20+ tests, documentation |

**Total**: 7 days (1 week)

---

## Next Steps

1. ✅ Design approval (this document)
2. Create tool skeleton
3. Implement JSON exporters
4. Add comprehensive tests
5. Document JSON schema
6. Integration proof-of-concept with VeriPG
7. Performance benchmarking
8. Production release

---

**End of Design Document**

