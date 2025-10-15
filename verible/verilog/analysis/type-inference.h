// Copyright 2025 The Verible Authors.
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

#ifndef VERIBLE_VERILOG_ANALYSIS_TYPE_INFERENCE_H_
#define VERIBLE_VERILOG_ANALYSIS_TYPE_INFERENCE_H_

#include <map>
#include <memory>

#include "verible/common/text/symbol.h"
#include "verible/common/text/token-info.h"
#include "verible/verilog/analysis/symbol-table.h"
#include "verible/verilog/analysis/type-representation.h"

namespace verilog {
namespace analysis {

// TypeInference provides type inference for SystemVerilog expressions.
// It builds on top of the SymbolTable and caches type information for performance.
//
// Usage:
//   TypeInference inference(&symbol_table);
//   const Type* expr_type = inference.InferType(*expression_node);
//   const Type* var_type = inference.GetDeclaredType(*symbol_node);
//
class TypeInference {
 public:
  // Construct TypeInference with a symbol table.
  // The symbol table must remain valid for the lifetime of TypeInference.
  explicit TypeInference(const SymbolTable* symbol_table);

  // Infer the type of an expression from the CST.
  // Returns nullptr if type cannot be inferred.
  // Results are cached for performance.
  const Type* InferType(const verible::Symbol& expr) const;

  // Get the declared type of a symbol from the symbol table.
  // Returns nullptr if symbol has no declared type.
  // Results are cached for performance.
  const Type* GetDeclaredType(const SymbolTableNode& symbol) const;

  // Infer type of a binary operation.
  // Returns the result type of (lhs op rhs).
  const Type* InferBinaryOp(const verible::Symbol& lhs,
                            const verible::Symbol& rhs,
                            const verible::TokenInfo& op) const;

  // Infer type of a unary operation.
  // Returns the result type of (op expr).
  const Type* InferUnaryOp(const verible::Symbol& expr,
                           const verible::TokenInfo& op) const;

  // Clear all caches. Call this if the symbol table is rebuilt.
  void ClearCache();

  // Statistics for debugging
  struct Stats {
    size_t cache_hits = 0;
    size_t cache_misses = 0;
    size_t total_inferences = 0;
  };
  const Stats& GetStats() const { return stats_; }

 private:
  // The symbol table (not owned)
  const SymbolTable* symbol_table_;

  // Cache: expression symbol -> inferred type
  // Key is the address of the Symbol node
  mutable std::map<const verible::Symbol*, std::unique_ptr<Type>> expr_cache_;

  // Cache: symbol table node -> declared type
  mutable std::map<const SymbolTableNode*, std::unique_ptr<Type>> decl_cache_;

  // Statistics
  mutable Stats stats_;

  // Internal inference methods (not cached)

  // Infer type from a literal token
  Type InferLiteral(const verible::TokenInfo& token) const;

  // Infer type from an identifier by looking up in symbol table
  const Type* InferIdentifier(const verible::Symbol& id) const;

  // Infer type from concatenation expression: {a, b, c}
  const Type* InferConcat(const verible::Symbol& concat) const;

  // Infer type from replication: {N{a}}
  const Type* InferReplication(const verible::Symbol& replication) const;

  // Infer type from bit/part select: a[3:0]
  const Type* InferSelect(const verible::Symbol& select) const;

  // Infer type from function call
  const Type* InferFunctionCall(const verible::Symbol& call) const;

  // Infer type from conditional expression: cond ? a : b
  const Type* InferConditional(const verible::Symbol& conditional) const;

  // Extract type information from DeclarationTypeInfo
  Type ExtractDeclaredType(const DeclarationTypeInfo& type_info) const;

  // Helper: Check cache, return cached value if found
  template <typename KeyType>
  const Type* CheckCache(
      const std::map<KeyType, std::unique_ptr<Type>>& cache,
      KeyType key) const {
    auto it = cache.find(key);
    if (it != cache.end()) {
      stats_.cache_hits++;
      return it->second.get();
    }
    stats_.cache_misses++;
    return nullptr;
  }

  // Helper: Store in cache
  template <typename KeyType>
  const Type* StoreInCache(std::map<KeyType, std::unique_ptr<Type>>& cache,
                           KeyType key, std::unique_ptr<Type> type) const {
    const Type* result = type.get();
    cache[key] = std::move(type);
    return result;
  }
};

}  // namespace analysis
}  // namespace verilog

#endif  // VERIBLE_VERILOG_ANALYSIS_TYPE_INFERENCE_H_

