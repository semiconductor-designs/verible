// Copyright 2017-2025 The Verible Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
/// - Uses std::unique_ptr for ownership
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

/// @brief Represents a location in source code
struct SourceLocation {
  /// @brief File path (absolute or relative to project root)
  std::string file_path;
  
  /// @brief Byte offset from start of file (0-indexed)
  int byte_start = -1;
  
  /// @brief Byte offset of end position (exclusive)
  int byte_end = -1;
  
  /// @brief Line number (1-indexed)
  int line = -1;
  
  /// @brief Column number (1-indexed)
  int column = -1;
  
  /// @brief Returns length in bytes
  int Length() const { return byte_end - byte_start; }
  
  /// @brief Checks if location is valid
  bool IsValid() const {
    return !file_path.empty() && 
           byte_start >= 0 && 
           byte_end >= byte_start &&
           line >= 1 && 
           column >= 1;
  }
};

/// @brief Type of variable reference (Kythe-specific)
enum class KytheReferenceType {
  /// @brief Variable is read (used in RHS expression)
  kRead,
  
  /// @brief Variable is written (used in LHS of assignment)
  kWrite,
  
  /// @brief Variable is both read and written
  kReadWrite,
  
  /// @brief Unknown or ambiguous reference type
  kUnknown
};

/// @brief Converts KytheReferenceType to string for JSON/display
inline const char* KytheReferenceTypeToString(KytheReferenceType type) {
  switch (type) {
    case KytheReferenceType::kRead: return "read";
    case KytheReferenceType::kWrite: return "write";
    case KytheReferenceType::kReadWrite: return "read_write";
    case KytheReferenceType::kUnknown: return "unknown";
  }
  return "unknown";
}

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

/// @brief Represents a single reference to a variable in source code
struct VariableReference {
  /// @brief Variable name (unqualified)
  std::string variable_name;
  
  /// @brief Fully qualified name with scope hierarchy
  std::string fully_qualified_name;
  
  /// @brief Source location of the reference
  SourceLocation location;
  
  /// @brief Type of reference (read, write, or both)
  KytheReferenceType type = KytheReferenceType::kUnknown;
  
  /// @brief Parent scope name
  std::string parent_scope;
  
  /// @brief Context information
  std::string context;
  
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

/// @brief Represents a variable declaration/definition in source code
struct VariableDefinition {
  /// @brief Variable name (unqualified)
  std::string variable_name;
  
  /// @brief Fully qualified name with scope hierarchy
  std::string fully_qualified_name;
  
  /// @brief Source location of the definition
  SourceLocation location;
  
  /// @brief Kind of variable
  VariableKind kind = VariableKind::kUnknown;
  
  /// @brief Data type as string
  std::string data_type;
  
  /// @brief Parent scope name
  std::string parent_scope;
  
  /// @brief Whether this is a port
  bool is_port = false;
  
  /// @brief Port direction (if is_port == true)
  std::string port_direction;
  
  /// @brief Whether this is a parameter or localparam
  bool is_parameter = false;
  
  /// @brief Whether this is a constant
  bool is_constant = false;
  
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

/// @brief Statistics about Kythe analysis
struct KytheStatistics {
  /// @brief Total number of variable references extracted
  int total_references = 0;
  
  /// @brief Total number of variable definitions extracted
  int total_definitions = 0;
  
  /// @brief Number of read-only references
  int read_references = 0;
  
  /// @brief Number of write-only references
  int write_references = 0;
  
  /// @brief Number of read-write references
  int read_write_references = 0;
  
  /// @brief Number of files analyzed
  int files_analyzed = 0;
  
  /// @brief Number of Kythe anchors processed
  int total_anchors = 0;
  
  /// @brief Total number of Kythe facts extracted
  int total_facts = 0;
  
  /// @brief Total number of Kythe edges processed
  int total_edges = 0;
  
  /// @brief Number of /kythe/edge/ref edges
  int ref_edges = 0;
  
  /// @brief Number of /kythe/edge/defines/binding edges
  int defines_edges = 0;
  
  /// @brief Analysis time in milliseconds
  int analysis_time_ms = 0;
  
  /// @brief Peak memory usage in MB (if measurable)
  int peak_memory_mb = 0;
  
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

/// @brief Analyzes SystemVerilog code to extract variable references using Kythe
///
/// This class wraps Verible's Kythe extractor and provides a simplified interface
/// for extracting variable references and definitions from SystemVerilog code.
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
  KytheAnalyzer(KytheAnalyzer&&) noexcept;
  KytheAnalyzer& operator=(KytheAnalyzer&&) noexcept;
  KytheAnalyzer(const KytheAnalyzer&) = delete;
  KytheAnalyzer& operator=(const KytheAnalyzer&) = delete;
  
  /// @brief Builds Kythe facts by analyzing the project
  ///
  /// @return absl::OkStatus() on success, error status otherwise
  absl::Status BuildKytheFacts();
  
  /// @brief Returns all extracted variable references
  const std::vector<VariableReference>& GetVariableReferences() const;
  
  /// @brief Returns all extracted variable definitions
  const std::vector<VariableDefinition>& GetVariableDefinitions() const;
  
  /// @brief Returns analysis statistics
  const KytheStatistics& GetStatistics() const;
  
  /// @brief Clears all analysis results
  void Clear();
  
  /// @brief Returns whether analysis has been performed
  bool IsAnalyzed() const;
  
 private:
  // Dependencies (non-owning pointers)
  const SymbolTable* symbol_table_;
  const VerilogProject* project_;
  
  // Analysis results
  std::vector<VariableReference> variable_references_;
  std::vector<VariableDefinition> variable_definitions_;
  KytheStatistics statistics_;
  
  // Internal state
  bool analyzed_;
  
  // Opaque pointer to Kythe internals (pimpl idiom)
  struct KytheInternals;
  std::unique_ptr<KytheInternals> internals_;
};

}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_KYTHE_ANALYZER_H_

