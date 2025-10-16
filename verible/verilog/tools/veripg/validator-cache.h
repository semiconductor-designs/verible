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

#ifndef VERIBLE_VERILOG_TOOLS_VERIPG_VALIDATOR_CACHE_H_
#define VERIBLE_VERILOG_TOOLS_VERIPG_VALIDATOR_CACHE_H_

#include <map>
#include <set>
#include <string>

namespace verilog {
namespace tools {

// Performance cache for type information and clock domains
class ValidatorCache {
 public:
  ValidatorCache() = default;
  
  // Type cache
  void CacheType(const std::string& symbol_name, const std::string& type_info);
  bool HasType(const std::string& symbol_name) const;
  std::string GetType(const std::string& symbol_name) const;
  
  // Clock domain cache
  void CacheClockDomain(const std::string& signal_name, const std::string& clock_domain);
  bool HasClockDomain(const std::string& signal_name) const;
  std::string GetClockDomain(const std::string& signal_name) const;
  
  // Reset signal cache
  void CacheResetSignal(const std::string& reset_name);
  bool IsResetSignal(const std::string& signal_name) const;
  const std::set<std::string>& GetResetSignals() const;
  
  // Clear all caches
  void Clear();
  
  // Get cache statistics
  struct CacheStats {
    int type_entries = 0;
    int clock_domain_entries = 0;
    int reset_signal_entries = 0;
  };
  
  CacheStats GetStatistics() const;
  
 private:
  std::map<std::string, std::string> type_cache_;
  std::map<std::string, std::string> clock_domain_cache_;
  std::set<std::string> reset_signals_;
};

}  // namespace tools
}  // namespace verilog

#endif  // VERIBLE_VERILOG_TOOLS_VERIPG_VALIDATOR_CACHE_H_

