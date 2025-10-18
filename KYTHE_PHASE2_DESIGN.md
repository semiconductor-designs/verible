# Kythe Integration - Phase 2: Design Document

**Date**: October 18, 2025  
**Phase**: 2 of 8  
**Status**: 🎨 Design In Progress  
**Philosophy**: "No hurry, 100%, Perfection, No skip, TDD"

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [Design Goals](#design-goals)
3. [KytheAnalyzer Class Design](#kytheanalyzer-class-design)
4. [Data Structures](#data-structures)
5. [JSON Schema Extension](#json-schema-extension)
6. [Integration Architecture](#integration-architecture)
7. [Test-Driven Design](#test-driven-design)
8. [Implementation Plan](#implementation-plan)

---

## Executive Summary

**Objective**: Design a complete, production-ready KytheAnalyzer that integrates Verible's Kythe extraction into the `verible-verilog-semantic` tool.

**Key Principles**:
- **Consistency**: Follow patterns from CallGraphEnhancer, DataFlowAnalyzer
- **Reusability**: Leverage existing Kythe infrastructure
- **Simplicity**: Clean API, minimal dependencies
- **Testability**: TDD-first, comprehensive test coverage
- **Performance**: Match existing analyzers (< 100ms for typical files)

**Deliverables**:
1. KytheAnalyzer class specification
2. Data structure definitions
3. JSON schema v1.1.0 specification
4. Integration design
5. Test specifications

---

## Design Goals

### Functional Goals

1. **Extract variable references** from SystemVerilog code
   - Track reads, writes, and read-write accesses
   - Maintain source location accuracy
   - Support all variable types (signals, ports, parameters)

2. **Extract variable definitions** 
   - Track declarations with full context
   - Associate with parent scopes

3. **Provide comprehensive statistics**
   - Total references/definitions counts
   - Per-file/per-module breakdowns

### Non-Functional Goals

1. **Performance**: < 100ms for typical files (< 1000 lines)
2. **Memory**: < 50 MB overhead per analysis
3. **Reliability**: 100% test coverage, no crashes
4. **Maintainability**: Clear code, comprehensive docs

### Integration Goals

1. **Seamless integration** with existing semantic tool
2. **Backward compatible** JSON schema evolution (1.0.0 → 1.1.0)
3. **VeriPG ready** output format

---

## KytheAnalyzer Class Design

### Class Overview

```cpp
/// @file kythe-analyzer.h
/// @brief Kythe-based variable reference extraction for SystemVerilog
///
/// This analyzer leverages Verible's existing Kythe extractor to provide
/// variable reference tracking (reads/writes) for semantic analysis tools.
///
/// Features:
/// - Variable reference extraction (reads, writes, read-write)
/// - Variable definition tracking with full source location
/// - Statistics and reporting
/// - Integration with verible-verilog-semantic tool
///
/// Memory Management:
/// - Uses std::unique_ptr for ownershi

p
/// - Exception-safe design
/// - RAII for resource management
///
/// @example Basic Usage
/// @code
/// #include "verible/verilog/analysis/kythe-analyzer.h"
/// 
/// verilog::VerilogProject project(".", {"design.sv"});
/// verilog::SymbolTable symbol_table(nullptr);
/// // ... build symbol table ...
/// 
/// verilog::KytheAnalyzer analyzer(symbol_table, project);
/// auto status = analyzer.BuildKytheFacts();
/// if (!status.ok()) {
///   std::cerr << "Error: " << status.message() << "\n";
///   return;
/// }
/// 
/// // Query results
/// const auto& refs = analyzer.GetVariableReferences();
/// for (const auto& ref : refs) {
///   std::cout << ref.variable_name << " at line " << ref.location.line << "\n";
/// }
/// @endcode

#ifndef VERIBLE_VERILOG_ANALYSIS_KYTHE_ANALYZER_H_
#define VERIBLE_VERILOG_ANALYSIS_KYTHE_ANALYZER_H_

#include <memory>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/verilog-project.h"

namespace verilog {

// Forward declarations
struct VariableReference;
struct VariableDefinition;
struct KytheStatistics;

/// @brief Analyzes SystemVerilog code to extract variable references using Kythe
///
/// This class wraps Verible's Kythe extractor and provides a simplified interface
/// for extracting variable references and definitions from SystemVerilog code.
/// It integrates seamlessly with the existing semantic analysis pipeline.
class KytheAnalyzer {
 public:
  /// @brief Constructs a KytheAnalyzer for the given symbol table and project
  ///
  /// @param symbol_table The symbol table built from the project
  /// @param project The Verilog project containing source files
  ///
  /// @note Does not take ownership of symbol_table or project
  /// @note Call BuildKytheFacts() after construction to perform analysis
  KytheAnalyzer(const SymbolTable& symbol_table, 
                const VerilogProject& project);
  
  /// @brief Destructor
  ~KytheAnalyzer();
  
  // Movable but not copyable
  KytheAnalyzer(KytheAnalyzer&&) = default;
  KytheAnalyzer& operator=(KytheAnalyzer&&) = default;
  KytheAnalyzer(const KytheAnalyzer&) = delete;
  KytheAnalyzer& operator=(const KytheAnalyzer&) = delete;
  
  /// @brief Builds Kythe facts by analyzing the project
  ///
  /// Performs the following steps:
  /// 1. Extracts Kythe facts from all source files
  /// 2. Filters for variable reference edges (/kythe/edge/ref)
  /// 3. Converts to VariableReference structures
  /// 4. Extracts variable definitions (/kythe/edge/defines/binding)
  /// 5. Computes statistics
  ///
  /// @return absl::OkStatus() on success, error status otherwise
  ///
  /// @note This method is idempotent - calling multiple times is safe
  /// @note Previous results are cleared before rebuilding
  ///
  /// @example
  /// @code
  /// KytheAnalyzer analyzer(symbol_table, project);
  /// if (auto status = analyzer.BuildKytheFacts(); !status.ok()) {
  ///   std::cerr << "Analysis failed: " << status.message() << "\n";
  /// }
  /// @endcode
  absl::Status BuildKytheFacts();
  
  //------------------------------------------------------------------------
  // Query Interface
  //------------------------------------------------------------------------
  
  /// @brief Returns all extracted variable references
  ///
  /// Variable references include reads, writes, and read-write accesses to:
  /// - Signals (logic, wire, reg)
  /// - Variables (int, bit, etc.)
  /// - Ports (input, output, inout)
  /// - Parameters and constants
  ///
  /// @return Const reference to vector of variable references
  /// @note Results are empty until BuildKytheFacts() succeeds
  const std::vector<VariableReference>& GetVariableReferences() const;
  
  /// @brief Returns all extracted variable definitions
  ///
  /// Variable definitions include declarations of:
  /// - Signals, variables, ports
  /// - Parameters and constants
  /// - Module/interface/class members
  ///
  /// @return Const reference to vector of variable definitions
  /// @note Results are empty until BuildKytheFacts() succeeds
  const std::vector<VariableDefinition>& GetVariableDefinitions() const;
  
  /// @brief Returns analysis statistics
  ///
  /// Statistics include:
  /// - Total reference/definition counts
  /// - Per-file/per-module breakdowns
  /// - Performance metrics
  ///
  /// @return Const reference to statistics structure
  const KytheStatistics& GetStatistics() const;
  
  //------------------------------------------------------------------------
  // Utility Methods
  //------------------------------------------------------------------------
  
  /// @brief Clears all analysis results
  ///
  /// Useful for re-analyzing or freeing memory. Call BuildKytheFacts()
  /// again to re-populate results.
  void Clear();
  
  /// @brief Returns whether analysis has been performed
  ///
  /// @return true if BuildKytheFacts() completed successfully
  bool IsAnalyzed() const;
  
 private:
  // Extraction implementation
  absl::Status ExtractKytheFacts();
  absl::Status ProcessKytheEdges();
  absl::Status ComputeStatistics();
  
  // Helper methods
  void ConvertKytheReferenceToVariableReference(
      const void* kythe_edge,  // kythe::Edge*
      VariableReference* output);
  
  void ConvertKytheDefinitionToVariableDefinition(
      const void* kythe_edge,  // kythe::Edge*
      VariableDefinition* output);
  
  // Dependencies (non-owning pointers)
  const SymbolTable* symbol_table_;
  const VerilogProject* project_;
  
  // Analysis results
  std::vector<VariableReference> variable_references_;
  std::vector<VariableDefinition> variable_definitions_;
  KytheStatistics statistics_;
  
  // Internal state
  bool analyzed_;
  
  // Opaque pointer to Kythe internals (pimpl idiom for clean separation)
  struct KytheInternals;
  std::unique_ptr<KytheInternals> internals_;
};

}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_KYTHE_ANALYZER_H_
```

### Design Rationale

**1. Constructor Pattern**: Matches CallGraphEnhancer
- Takes const references to SymbolTable and VerilogProject
- Doesn't perform analysis in constructor (explicit BuildKytheFacts() call)
- Allows validation and error handling

**2. Move-Only Semantics**: Matches DataFlowAnalyzer
- Prevents accidental copies (expensive)
- Supports efficient transfer of ownership
- std::unique_ptr for internal data

**3. Pimpl Idiom**: For Kythe internals
- Hides Kythe implementation details
- Reduces header dependencies
- Allows future refactoring without API changes

**4. Error Handling**: absl::Status return
- Consistent with Verible conventions
- Allows detailed error messages
- Supports status_or pattern if needed

**5. Query Interface**: Const references
- Zero-copy access to results
- Clear ownership semantics
- Safe for concurrent reads (after analysis)

---

## Data Structures

### VariableReference

```cpp
/// @brief Represents a single reference to a variable in source code
///
/// A variable reference is any use of a variable in an expression,
/// including reads, writes, and read-write accesses.
struct VariableReference {
  /// @brief Variable name (unqualified)
  ///
  /// Examples: "data", "clk", "current_state"
  std::string variable_name;
  
  /// @brief Fully qualified name with scope hierarchy
  ///
  /// Examples: 
  /// - "module::data"
  /// - "top::sub::signal"
  /// - "pkg::MyClass::member"
  std::string fully_qualified_name;
  
  /// @brief Source location of the reference
  SourceLocation location;
  
  /// @brief Type of reference (read, write, or both)
  ReferenceType type;
  
  /// @brief Parent scope name
  ///
  /// The module, class, or function containing this reference.
  /// Examples: "my_module", "my_package::MyClass"
  std::string parent_scope;
  
  /// @brief Context information
  ///
  /// Additional context about where/how the reference appears:
  /// - "always_comb" - in combinational block
  /// - "always_ff" - in sequential block
  /// - "assign" - in continuous assignment
  /// - "case" - in case statement
  /// - "function" - in function body
  std::string context;
  
  //------------------------------------------------------------------------
  // Comparison operators for sorting/searching
  //------------------------------------------------------------------------
  
  bool operator==(const VariableReference& other) const {
    return variable_name == other.variable_name &&
           location.file_path == other.location.file_path &&
           location.byte_start == other.location.byte_start;
  }
  
  bool operator<(const VariableReference& other) const {
    if (location.file_path != other.location.file_path)
      return location.file_path < other.location.file_path;
    if (location.line != other.location.line)
      return location.line < other.location.line;
    return location.column < other.location.column;
  }
};
```

### VariableDefinition

```cpp
/// @brief Represents a variable declaration/definition in source code
struct VariableDefinition {
  /// @brief Variable name (unqualified)
  std::string variable_name;
  
  /// @brief Fully qualified name with scope hierarchy
  std::string fully_qualified_name;
  
  /// @brief Source location of the definition
  SourceLocation location;
  
  /// @brief Kind of variable
  VariableKind kind;
  
  /// @brief Data type as string
  ///
  /// Examples: "logic", "logic [7:0]", "int", "my_type_t"
  std::string data_type;
  
  /// @brief Parent scope name
  std::string parent_scope;
  
  /// @brief Whether this is a port
  bool is_port;
  
  /// @brief Port direction (if is_port == true)
  ///
  /// One of: "input", "output", "inout", "" (empty if not a port)
  std::string port_direction;
  
  /// @brief Whether this is a parameter or localparam
  bool is_parameter;
  
  /// @brief Whether this is a constant (const keyword or parameter)
  bool is_constant;
  
  //------------------------------------------------------------------------
  // Comparison operators
  //------------------------------------------------------------------------
  
  bool operator==(const VariableDefinition& other) const {
    return variable_name == other.variable_name &&
           fully_qualified_name == other.fully_qualified_name &&
           location.file_path == other.location.file_path;
  }
  
  bool operator<(const VariableDefinition& other) const {
    if (location.file_path != other.location.file_path)
      return location.file_path < other.location.file_path;
    return fully_qualified_name < other.fully_qualified_name;
  }
};
```

### SourceLocation

```cpp
/// @brief Represents a location in source code with multiple representations
struct SourceLocation {
  /// @brief File path (absolute or relative to project root)
  std::string file_path;
  
  /// @brief Byte offset from start of file (0-indexed)
  int byte_start;
  
  /// @brief Byte offset of end position (exclusive)
  int byte_end;
  
  /// @brief Line number (1-indexed)
  int line;
  
  /// @brief Column number (1-indexed)
  int column;
  
  /// @brief Length in bytes
  int Length() const { return byte_end - byte_start; }
  
  /// @brief Checks if location is valid
  bool IsValid() const {
    return !file_path.empty() && 
           byte_start >= 0 && 
           byte_end >= byte_start &&
           line >= 1 && 
           column >= 1;
  }
  
  //------------------------------------------------------------------------
  // Factory methods for conversion
  //------------------------------------------------------------------------
  
  /// @brief Creates SourceLocation from Kythe anchor
  ///
  /// Kythe anchors use byte offsets. This converts to line:column using
  /// the source file content.
  ///
  /// @param file_path Path to source file
  /// @param anchor_start Byte offset start (from Kythe)
  /// @param anchor_end Byte offset end (from Kythe)
  /// @param file_content Source file content for line/column computation
  /// @return SourceLocation with all fields populated
  static SourceLocation FromKytheAnchor(
      absl::string_view file_path,
      int anchor_start,
      int anchor_end,
      absl::string_view file_content);
};
```

### ReferenceType

```cpp
/// @brief Type of variable reference
enum class ReferenceType {
  /// @brief Variable is read (used in RHS expression)
  kRead,
  
  /// @brief Variable is written (used in LHS of assignment)
  kWrite,
  
  /// @brief Variable is both read and written
  ///
  /// Examples:
  /// - x += 1;  (read old value, write new value)
  /// - x++;     (read, increment, write)
  /// - x = f(x); (read x in function call, write result)
  kReadWrite,
  
  /// @brief Unknown or ambiguous reference type
  kUnknown
};

/// @brief Converts ReferenceType to string for JSON/display
inline const char* ReferenceTypeToString(ReferenceType type) {
  switch (type) {
    case ReferenceType::kRead: return "read";
    case ReferenceType::kWrite: return "write";
    case ReferenceType::kReadWrite: return "read_write";
    case ReferenceType::kUnknown: return "unknown";
  }
  return "unknown";
}

/// @brief Parses ReferenceType from string
inline ReferenceType StringToReferenceType(absl::string_view str) {
  if (str == "read") return ReferenceType::kRead;
  if (str == "write") return ReferenceType::kWrite;
  if (str == "read_write") return ReferenceType::kReadWrite;
  return ReferenceType::kUnknown;
}
```

### VariableKind

```cpp
/// @brief Kind/category of variable
enum class VariableKind {
  /// @brief Signal (logic, wire, reg, bit)
  kSignal,
  
  /// @brief Variable (int, shortint, longint, byte, integer, time, real, etc.)
  kVariable,
  
  /// @brief Port (input, output, inout)
  kPort,
  
  /// @brief Parameter or localparam
  kParameter,
  
  /// @brief Enum constant
  kEnumConstant,
  
  /// @brief Class member
  kClassMember,
  
  /// @brief Module/interface instance
  kInstance,
  
  /// @brief Unknown kind
  kUnknown
};

/// @brief Converts VariableKind to string
inline const char* VariableKindToString(VariableKind kind) {
  switch (kind) {
    case VariableKind::kSignal: return "signal";
    case VariableKind::kVariable: return "variable";
    case VariableKind::kPort: return "port";
    case VariableKind::kParameter: return "parameter";
    case VariableKind::kEnumConstant: return "enum_constant";
    case VariableKind::kClassMember: return "class_member";
    case VariableKind::kInstance: return "instance";
    case VariableKind::kUnknown: return "unknown";
  }
  return "unknown";
}
```

### KytheStatistics

```cpp
/// @brief Statistics about Kythe analysis
struct KytheStatistics {
  /// @brief Total number of variable references extracted
  int total_references;
  
  /// @brief Total number of variable definitions extracted
  int total_definitions;
  
  /// @brief Number of read-only references
  int read_references;
  
  /// @brief Number of write-only references
  int write_references;
  
  /// @brief Number of read-write references
  int read_write_references;
  
  /// @brief Number of files analyzed
  int files_analyzed;
  
  /// @brief Number of Kythe anchors processed
  int total_anchors;
  
  /// @brief Total number of Kythe facts extracted
  int total_facts;
  
  /// @brief Total number of Kythe edges processed
  int total_edges;
  
  /// @brief Number of /kythe/edge/ref edges
  int ref_edges;
  
  /// @brief Number of /kythe/edge/defines/binding edges
  int defines_edges;
  
  /// @brief Analysis time in milliseconds
  int analysis_time_ms;
  
  /// @brief Peak memory usage in MB (if measurable)
  int peak_memory_mb;
  
  //------------------------------------------------------------------------
  // Utility methods
  //------------------------------------------------------------------------
  
  /// @brief Resets all statistics to zero
  void Clear() {
    *this = KytheStatistics{};
  }
  
  /// @brief Returns average references per file
  double AverageReferencesPerFile() const {
    return files_analyzed > 0 
        ? static_cast<double>(total_references) / files_analyzed 
        : 0.0;
  }
  
  /// @brief Returns average definitions per file
  double AverageDefinitionsPerFile() const {
    return files_analyzed > 0 
        ? static_cast<double>(total_definitions) / files_analyzed 
        : 0.0;
  }
};
```

---

## JSON Schema Extension

### Schema Version Evolution

**Current**: v1.0.0 (CallGraph, DataFlow, Unused)  
**New**: v1.1.0 (adds Kythe)

**Versioning Strategy**:
- **Major version** (1.x.x): Breaking changes
- **Minor version** (x.1.x): New features (backward compatible)
- **Patch version** (x.x.1): Bug fixes

**v1.1.0 is backward compatible**: Tools reading v1.0.0 can ignore the new "kythe" field.

### Complete JSON Schema v1.1.0

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "Verible Semantic Analysis Output",
  "version": "1.1.0",
  "type": "object",
  "required": ["schema_version"],
  "properties": {
    "schema_version": {
      "type": "string",
      "enum": ["1.0.0", "1.1.0"],
      "description": "JSON schema version for backward compatibility"
    },
    "call_graph": {
      "type": "object",
      "description": "Call graph analysis (v1.0.0 feature)",
      "properties": {
        "version": {"type": "string", "const": "1.0.0"},
        "nodes": {"type": "array"},
        "edges": {"type": "array"},
        "statistics": {"type": "object"}
      }
    },
    "data_flow": {
      "type": "object",
      "description": "Data flow analysis (v1.0.0 feature)",
      "properties": {
        "version": {"type": "string", "const": "1.0.0"},
        "nodes": {"type": "array"},
        "edges": {"type": "array"},
        "statistics": {"type": "object"}
      }
    },
    "unused": {
      "type": "object",
      "description": "Unused entity detection (v1.0.0 feature)",
      "properties": {
        "version": {"type": "string", "const": "1.0.0"},
        "entities": {"type": "array"},
        "statistics": {"type": "object"}
      }
    },
    "kythe": {
      "type": "object",
      "description": "Kythe variable reference analysis (NEW in v1.1.0)",
      "required": ["version", "variable_references", "variable_definitions", "statistics"],
      "properties": {
        "version": {
          "type": "string",
          "const": "1.0.0",
          "description": "Kythe analyzer version"
        },
        "variable_references": {
          "type": "array",
          "description": "All variable references (reads/writes)",
          "items": {
            "type": "object",
            "required": ["variable_name", "fully_qualified_name", "location", "type"],
            "properties": {
              "variable_name": {
                "type": "string",
                "description": "Variable name (unqualified)",
                "example": "current_state"
              },
              "fully_qualified_name": {
                "type": "string",
                "description": "Full hierarchical name",
                "example": "fsm::current_state"
              },
              "location": {
                "type": "object",
                "required": ["file", "byte_start", "byte_end", "line", "column"],
                "properties": {
                  "file": {
                    "type": "string",
                    "description": "Source file path"
                  },
                  "byte_start": {
                    "type": "integer",
                    "minimum": 0,
                    "description": "Byte offset start (0-indexed)"
                  },
                  "byte_end": {
                    "type": "integer",
                    "minimum": 0,
                    "description": "Byte offset end (exclusive)"
                  },
                  "line": {
                    "type": "integer",
                    "minimum": 1,
                    "description": "Line number (1-indexed)"
                  },
                  "column": {
                    "type": "integer",
                    "minimum": 1,
                    "description": "Column number (1-indexed)"
                  }
                }
              },
              "type": {
                "type": "string",
                "enum": ["read", "write", "read_write", "unknown"],
                "description": "Reference type"
              },
              "parent_scope": {
                "type": "string",
                "description": "Containing scope (module/class/function)"
              },
              "context": {
                "type": "string",
                "description": "Context (always_comb, always_ff, assign, etc.)"
              }
            }
          }
        },
        "variable_definitions": {
          "type": "array",
          "description": "All variable declarations/definitions",
          "items": {
            "type": "object",
            "required": ["variable_name", "fully_qualified_name", "location", "kind"],
            "properties": {
              "variable_name": {"type": "string"},
              "fully_qualified_name": {"type": "string"},
              "location": {
                "type": "object",
                "required": ["file", "byte_start", "byte_end", "line", "column"],
                "properties": {
                  "file": {"type": "string"},
                  "byte_start": {"type": "integer", "minimum": 0},
                  "byte_end": {"type": "integer", "minimum": 0},
                  "line": {"type": "integer", "minimum": 1},
                  "column": {"type": "integer", "minimum": 1}
                }
              },
              "kind": {
                "type": "string",
                "enum": ["signal", "variable", "port", "parameter", "enum_constant", "class_member", "instance", "unknown"]
              },
              "data_type": {"type": "string"},
              "parent_scope": {"type": "string"},
              "is_port": {"type": "boolean"},
              "port_direction": {"type": "string", "enum": ["input", "output", "inout", ""]},
              "is_parameter": {"type": "boolean"},
              "is_constant": {"type": "boolean"}
            }
          }
        },
        "statistics": {
          "type": "object",
          "required": ["total_references", "total_definitions"],
          "properties": {
            "total_references": {"type": "integer", "minimum": 0},
            "total_definitions": {"type": "integer", "minimum": 0},
            "read_references": {"type": "integer", "minimum": 0},
            "write_references": {"type": "integer", "minimum": 0},
            "read_write_references": {"type": "integer", "minimum": 0},
            "files_analyzed": {"type": "integer", "minimum": 0},
            "total_anchors": {"type": "integer", "minimum": 0},
            "total_facts": {"type": "integer", "minimum": 0},
            "total_edges": {"type": "integer", "minimum": 0},
            "ref_edges": {"type": "integer", "minimum": 0},
            "defines_edges": {"type": "integer", "minimum": 0},
            "analysis_time_ms": {"type": "integer", "minimum": 0},
            "peak_memory_mb": {"type": "integer", "minimum": 0}
          }
        }
      }
    }
  }
}
```

### Example JSON Output

```json
{
  "schema_version": "1.1.0",
  "kythe": {
    "version": "1.0.0",
    "variable_references": [
      {
        "variable_name": "current_state",
        "fully_qualified_name": "fsm::current_state",
        "location": {
          "file": "fsm.sv",
          "byte_start": 185,
          "byte_end": 198,
          "line": 10,
          "column": 8
        },
        "type": "read",
        "parent_scope": "fsm",
        "context": "case"
      },
      {
        "variable_name": "next_state",
        "fully_qualified_name": "fsm::next_state",
        "location": {
          "file": "fsm.sv",
          "byte_start": 210,
          "byte_end": 220,
          "line": 11,
          "column": 10
        },
        "type": "write",
        "parent_scope": "fsm",
        "context": "always_comb"
      }
    ],
    "variable_definitions": [
      {
        "variable_name": "current_state",
        "fully_qualified_name": "fsm::current_state",
        "location": {
          "file": "fsm.sv",
          "byte_start": 95,
          "byte_end": 108,
          "line": 5,
          "column": 10
        },
        "kind": "signal",
        "data_type": "state_t",
        "parent_scope": "fsm",
        "is_port": false,
        "port_direction": "",
        "is_parameter": false,
        "is_constant": false
      }
    ],
    "statistics": {
      "total_references": 20,
      "total_definitions": 7,
      "read_references": 12,
      "write_references": 5,
      "read_write_references": 3,
      "files_analyzed": 1,
      "total_anchors": 31,
      "total_facts": 154,
      "total_edges": 45,
      "ref_edges": 20,
      "defines_edges": 7,
      "analysis_time_ms": 95,
      "peak_memory_mb": 12
    }
  }
}
```

---

## Integration Architecture

### Component Diagram

```
┌──────────────────────────────────────────────────────────────┐
│                 verible-verilog-semantic                      │
│                   (Command-Line Tool)                         │
└───────────────────────┬──────────────────────────────────────┘
                        │
                        │ --include_kythe flag
                        ↓
┌──────────────────────────────────────────────────────────────┐
│              verible-verilog-semantic.cc                      │
│                 (Main Implementation)                         │
│                                                               │
│  1. Parse flags                                               │
│  2. Build SymbolTable                                         │
│  3. IF --include_kythe:                                       │
│     - Create KytheAnalyzer                                    │
│     - Call BuildKytheFacts()                                  │
│     - Get results                                             │
│  4. Export to JSON                                            │
└───────────────────────┬──────────────────────────────────────┘
                        │
            ┌───────────┴───────────┐
            │                       │
            ↓                       ↓
┌───────────────────────┐  ┌───────────────────────┐
│   KytheAnalyzer       │  │  SemanticJsonExporter │
│  (New Component)      │  │   (Updated)           │
│                       │  │                       │
│ - BuildKytheFacts()   │  │ - ExportKythe()       │
│ - GetVariableRefs()   │  │   (new method)        │
│ - GetVariableDefs()   │  │                       │
│ - GetStatistics()     │  └───────────────────────┘
└───────────┬───────────┘
            │
            │ uses
            ↓
┌───────────────────────────────────────────────────────────────┐
│              Existing Kythe Infrastructure                     │
│                                                                │
│  - kythe-facts-extractor.h/cc                                 │
│  - indexing-facts-tree-extractor.h/cc                         │
│  - kythe-facts.h/cc (VName, Fact, Edge structures)            │
│                                                                │
│  Functions:                                                    │
│  - ExtractFiles() - extracts facts from files                 │
│  - StreamKytheFactsEntries() - streams facts                  │
└────────────────────────────────────────────────────────────────┘
```

### Data Flow

```
Input: design.sv
    │
    ↓
[VerilogProject]
    │
    ↓
[SymbolTable] ←─────┐
    │               │
    ↓               │
[KytheAnalyzer]     │
    │               │
    ├─→ ExtractFiles()  (calls existing Kythe extractor)
    │
    ├─→ [IndexingFactsTree]
    │       │
    │       ├─→ Filter /kythe/edge/ref edges
    │       ├─→ Filter /kythe/edge/defines/binding edges
    │       └─→ Extract anchors
    │
    ├─→ Convert to VariableReference structures
    ├─→ Convert to VariableDefinition structures
    ├─→ Compute statistics
    │
    ↓
[Results: variable_references_, variable_definitions_, statistics_]
    │
    ↓
[SemanticJsonExporter::ExportKythe()]
    │
    ↓
JSON Output (schema v1.1.0)
```

### File Organization

```
verible/verilog/analysis/
├── kythe-analyzer.h          (NEW - class declaration)
├── kythe-analyzer.cc         (NEW - implementation)
├── kythe-analyzer_test.cc    (NEW - unit tests)
└── BUILD                     (UPDATED - add kythe-analyzer target)

verible/verilog/tools/semantic/
├── json-exporter.h           (UPDATED - add ExportKythe())
├── json-exporter.cc          (UPDATED - implement ExportKythe())
├── json-exporter_test.cc     (UPDATED - add Kythe tests)
├── verible-verilog-semantic.cc  (UPDATED - integrate KytheAnalyzer)
├── JSON_SCHEMA.md            (UPDATED - add Kythe section)
├── README.md                 (UPDATED - document --include_kythe)
└── BUILD                     (UPDATED - add dependencies)
```

---

## Test-Driven Design

### Test Strategy

**Philosophy**: Write tests FIRST, then implement to pass them.

**Test Pyramid**:
```
         ╱╲
        ╱  ╲  Integration Tests (5)
       ╱────╲
      ╱      ╲ Unit Tests (30+)
     ╱────────╲
    ╱          ╲ Smoke Tests (10)
   ╱────────────╲
```

### Test Specifications

#### 1. Smoke Tests (10 tests)

**Purpose**: Validate basic functionality

**Tests**:
1. `EmptyModule` - KytheAnalyzer on empty module (no crash)
2. `SingleSignal` - One signal declaration (1 definition)
3. `SingleReference` - One variable read (1 reference)
4. `SingleAssignment` - One variable write (1 reference)
5. `ReadAndWrite` - Variable read and written (2 references)
6. `MultipleVariables` - Multiple variables (counts match)
7. `FSMBasic` - Simple FSM (state vars + enum constants)
8. `ParameterUsage` - Parameter references
9. `PortUsage` - Port references
10. `Statistics` - Statistics are computed correctly

#### 2. Unit Tests (30+ tests)

**FR-1: Basic Variable References** (6 tests)
- `BasicRead` - Variable read in expression
- `BasicWrite` - Variable write in assignment
- `MultipleReads` - Same variable read multiple times
- `MultipleWrites` - Same variable written multiple times
- `DifferentVariables` - Multiple different variables
- `LocationAccuracy` - Source locations are accurate

**FR-2: FSM Variable References** (8 tests)
- `FSMStateVars` - Current/next state references
- `FSMEnumConstants` - Enum constant (IDLE, BUSY, DONE) references
- `FSMAlwaysFF` - State register references
- `FSMAlwaysComb` - Next state logic references
- `FSMCaseStatement` - Case expression references
- `FSMComplexTransitions` - Multiple state transitions
- `FSMNestedCase` - Nested case statements
- `FSMMultipleFSMs` - Multiple FSMs in same module

**FR-3: Cross-Module References** (4 tests)
- `PortConnection` - Port references in instantiation
- `MultiFileAnalysis` - References across multiple files
- `HierarchicalScope` - Fully qualified names
- `ModuleInterfaces` - Interface port references

**FR-4: Location Accuracy** (6 tests)
- `ByteOffsetAccuracy` - Byte offsets match source
- `LineColumnAccuracy` - Line:column conversion correct
- `MultilineExpression` - References span multiple lines
- `WhitespaceHandling` - Whitespace doesn't affect offsets
- `TabHandling` - Tabs handled correctly
- `UnicodeHandling` - Unicode characters handled

**FR-5: Hierarchical References** (3 tests)
- `InstanceReference` - Instance.signal references
- `FullyQualifiedNames` - FQN generation correct
- `NestedScopes` - Multiple level hierarchy

**FR-6: Complex Types** (3 tests)
- `ArrayReferences` - Array element references
- `StructReferences` - Struct member references
- `UnpackedArrays` - Unpacked array handling

#### 3. Integration Tests (5 tests)

**Purpose**: End-to-end validation

**Tests**:
1. `ToolIntegration` - verible-verilog-semantic --include_kythe works
2. `JSONSchemaValid` - Output matches JSON schema
3. `VeriPGCompatibility` - Output consumable by VeriPG
4. `PerformanceBenchmark` - Performance meets targets
5. `OpenTitanSmoke` - Works on real OpenTitan file

### Test Template

```cpp
// Test template following TDD approach
TEST(KytheAnalyzerTest, TestName) {
  // ARRANGE: Set up test data
  const char* code = R"(
    module test;
      logic sig;
      assign sig = 1'b0;
    endmodule
  )";
  
  InMemoryVerilogSourceFile file("test.sv", code);
  VerilogProject project(".");
  project.AddVirtualFile("test.sv", code);
  
  SymbolTable symbol_table(/* root_symbol= */ nullptr);
  // ... build symbol table from file ...
  
  // ACT: Perform analysis
  KytheAnalyzer analyzer(symbol_table, project);
  const auto status = analyzer.BuildKytheFacts();
  
  // ASSERT: Verify results
  ASSERT_TRUE(status.ok()) << status.message();
  
  const auto& refs = analyzer.GetVariableReferences();
  EXPECT_GE(refs.size(), 1) << "Expected at least 1 reference";
  
  // Verify specific reference
  bool found_sig = false;
  for (const auto& ref : refs) {
    if (ref.variable_name == "sig") {
      found_sig = true;
      EXPECT_EQ(ref.type, ReferenceType::kWrite);
      EXPECT_TRUE(ref.location.IsValid());
    }
  }
  EXPECT_TRUE(found_sig) << "Did not find 'sig' reference";
}
```

---

## Implementation Plan

### Phase 3 Tasks (Days 4-6)

**Day 4: Core Implementation**
1. Create `kythe-analyzer.h` with full class declaration
2. Create `kythe-analyzer.cc` stub implementation
3. Create `kythe-analyzer_test.cc` with FR-1 tests (6 tests)
4. Implement `BuildKytheFacts()` to pass FR-1 tests
5. Run tests: Expect 6/6 pass

**Day 5: Complete Implementation**
1. Add FR-2 tests (8 tests) to `kythe-analyzer_test.cc`
2. Implement FSM support in `BuildKytheFacts()`
3. Add FR-4 tests (6 tests)
4. Implement location accuracy
5. Run tests: Expect 20/20 pass

**Day 6: JSON Integration**
1. Update `json-exporter.h` - add `ExportKythe()` method
2. Implement `ExportKythe()` in `json-exporter.cc`
3. Add JSON export tests (5 tests) to `json-exporter_test.cc`
4. Update `verible-verilog-semantic.cc` - add `--include_kythe` flag
5. Run all tests: Expect 25/25 pass

### Success Criteria for Phase 2

- [ ] Complete class design documented
- [ ] All data structures specified
- [ ] JSON schema v1.1.0 defined
- [ ] Integration architecture designed
- [ ] Test specifications written (45+ tests)
- [ ] Implementation plan detailed

### Transition to Phase 3

**Prerequisites**:
- Phase 2 design reviewed
- All TODOs updated
- Design document committed to git

**First Implementation Task**:
Create `kythe-analyzer.h` with full class declaration from this design.

---

## Conclusion

**Phase 2 Design Status**: ✅ **COMPLETE**

**Key Deliverables**:
1. ✅ KytheAnalyzer class fully designed
2. ✅ Data structures specified
3. ✅ JSON schema v1.1.0 defined
4. ✅ Integration architecture designed
5. ✅ Test specifications written (45+ tests)
6. ✅ Implementation plan ready

**Design Quality**:
- **Consistency**: Follows CallGraphEnhancer/DataFlowAnalyzer patterns
- **Completeness**: All requirements addressed
- **Clarity**: Clear API, comprehensive docs
- **Testability**: TDD-first with 45+ test specifications

**Next Phase**: Phase 3 - Core Implementation (Days 4-6)

**Estimated Effort**: 
- Phase 3: 12-15 hours
- Confidence: HIGH (design is solid)

---

**Document Status**: ✅ Phase 2 Design Complete  
**Author**: AI Assistant  
**Date**: October 18, 2025  
**Review Status**: Ready for implementation  
**Next Action**: Create kythe-analyzer.h file

