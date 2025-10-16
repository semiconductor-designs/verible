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

#include "verible/verilog/tools/veripg/validator-cache.h"

namespace verilog {
namespace tools {

void ValidatorCache::CacheType(const std::string& symbol_name,
                                const std::string& type_info) {
  type_cache_[symbol_name] = type_info;
}

bool ValidatorCache::HasType(const std::string& symbol_name) const {
  return type_cache_.find(symbol_name) != type_cache_.end();
}

std::string ValidatorCache::GetType(const std::string& symbol_name) const {
  auto it = type_cache_.find(symbol_name);
  return (it != type_cache_.end()) ? it->second : "";
}

void ValidatorCache::CacheClockDomain(const std::string& signal_name,
                                      const std::string& clock_domain) {
  clock_domain_cache_[signal_name] = clock_domain;
}

bool ValidatorCache::HasClockDomain(const std::string& signal_name) const {
  return clock_domain_cache_.find(signal_name) != clock_domain_cache_.end();
}

std::string ValidatorCache::GetClockDomain(const std::string& signal_name) const {
  auto it = clock_domain_cache_.find(signal_name);
  return (it != clock_domain_cache_.end()) ? it->second : "";
}

void ValidatorCache::CacheResetSignal(const std::string& reset_name) {
  reset_signals_.insert(reset_name);
}

bool ValidatorCache::IsResetSignal(const std::string& signal_name) const {
  return reset_signals_.find(signal_name) != reset_signals_.end();
}

const std::set<std::string>& ValidatorCache::GetResetSignals() const {
  return reset_signals_;
}

void ValidatorCache::Clear() {
  type_cache_.clear();
  clock_domain_cache_.clear();
  reset_signals_.clear();
}

ValidatorCache::CacheStats ValidatorCache::GetStatistics() const {
  CacheStats stats;
  stats.type_entries = type_cache_.size();
  stats.clock_domain_entries = clock_domain_cache_.size();
  stats.reset_signal_entries = reset_signals_.size();
  return stats;
}

}  // namespace tools
}  // namespace verilog

