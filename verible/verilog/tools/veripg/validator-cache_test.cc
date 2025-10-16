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

#include "gtest/gtest.h"

namespace verilog {
namespace tools {
namespace {

// Test: Type caching
TEST(ValidatorCacheTest, TypeCaching) {
  ValidatorCache cache;
  
  // Initially empty
  EXPECT_FALSE(cache.HasType("my_signal"));
  
  // Cache a type
  cache.CacheType("my_signal", "logic [7:0]");
  EXPECT_TRUE(cache.HasType("my_signal"));
  EXPECT_EQ(cache.GetType("my_signal"), "logic [7:0]");
  
  // Unknown types return empty
  EXPECT_EQ(cache.GetType("unknown"), "");
}

// Test: Clock domain caching
TEST(ValidatorCacheTest, ClockDomainCaching) {
  ValidatorCache cache;
  
  // Initially empty
  EXPECT_FALSE(cache.HasClockDomain("data_signal"));
  
  // Cache clock domain
  cache.CacheClockDomain("data_signal", "clk_fast");
  EXPECT_TRUE(cache.HasClockDomain("data_signal"));
  EXPECT_EQ(cache.GetClockDomain("data_signal"), "clk_fast");
  
  // Unknown domains return empty
  EXPECT_EQ(cache.GetClockDomain("unknown"), "");
}

// Test: Reset signal caching
TEST(ValidatorCacheTest, ResetSignalCaching) {
  ValidatorCache cache;
  
  // Initially empty
  EXPECT_FALSE(cache.IsResetSignal("rst_n"));
  
  // Cache reset signals
  cache.CacheResetSignal("rst_n");
  cache.CacheResetSignal("rst_async");
  
  EXPECT_TRUE(cache.IsResetSignal("rst_n"));
  EXPECT_TRUE(cache.IsResetSignal("rst_async"));
  EXPECT_FALSE(cache.IsResetSignal("clk"));
  
  // Check set size
  EXPECT_EQ(cache.GetResetSignals().size(), 2);
}

// Test: Clear cache
TEST(ValidatorCacheTest, ClearCache) {
  ValidatorCache cache;
  
  // Populate cache
  cache.CacheType("signal1", "logic");
  cache.CacheClockDomain("signal2", "clk");
  cache.CacheResetSignal("rst");
  
  auto stats_before = cache.GetStatistics();
  EXPECT_GT(stats_before.type_entries, 0);
  EXPECT_GT(stats_before.clock_domain_entries, 0);
  EXPECT_GT(stats_before.reset_signal_entries, 0);
  
  // Clear
  cache.Clear();
  
  auto stats_after = cache.GetStatistics();
  EXPECT_EQ(stats_after.type_entries, 0);
  EXPECT_EQ(stats_after.clock_domain_entries, 0);
  EXPECT_EQ(stats_after.reset_signal_entries, 0);
}

// Test: Statistics
TEST(ValidatorCacheTest, Statistics) {
  ValidatorCache cache;
  
  cache.CacheType("s1", "logic");
  cache.CacheType("s2", "logic [3:0]");
  cache.CacheClockDomain("s1", "clk_a");
  cache.CacheResetSignal("rst_n");
  
  auto stats = cache.GetStatistics();
  EXPECT_EQ(stats.type_entries, 2);
  EXPECT_EQ(stats.clock_domain_entries, 1);
  EXPECT_EQ(stats.reset_signal_entries, 1);
}

}  // namespace
}  // namespace tools
}  // namespace verilog

