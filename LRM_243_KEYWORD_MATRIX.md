# SystemVerilog LRM Complete Keyword Matrix (243 Keywords)

**Source:** IEEE 1800-2017 Standard  
**Version:** v3.8.0 verification  
**Date:** 2025-10-14

---

## Category 1: Structural Keywords (20)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 1 | `module` | 1 | ✅ | Core |
| 2 | `endmodule` | 2 | ✅ | Core |
| 3 | `interface` | 3 | ✅ | SV |
| 4 | `endinterface` | 4 | ✅ | SV |
| 5 | `package` | 5 | ✅ | SV |
| 6 | `endpackage` | 6 | ✅ | SV |
| 7 | `program` | 7 | ✅ | SV |
| 8 | `endprogram` | 8 | ✅ | SV |
| 9 | `primitive` | 9 | ✅ | Core (UDP) |
| 10 | `endprimitive` | 10 | ✅ | Core (UDP) |
| 11 | `table` | 11 | ✅ | Core (UDP) |
| 12 | `endtable` | 12 | ✅ | Core (UDP) |
| 13 | `generate` | 13 | ✅ | SV |
| 14 | `endgenerate` | 14 | ✅ | SV |
| 15 | `modport` | 15 | ✅ | SV |
| 16 | `checker` | 16 | ✅ | SV |
| 17 | `endchecker` | 17 | ✅ | SV |
| 18 | `clocking` | 18 | ✅ | SV |
| 19 | `endclocking` | 19 | ✅ | SV |
| 20 | `specify` | 20 | ✅ | Core |
| 21 | `endspecify` | 21 | ✅ | Core |

**Expected:** 20/20 (already implemented)

---

## Category 2: Data Types (32)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 22 | `wire` | 100 | ✅ | Core |
| 23 | `reg` | 101 | ✅ | Core |
| 24 | `logic` | 102 | ✅ | SV |
| 25 | `bit` | 103 | ✅ | SV |
| 26 | `byte` | 104 | ✅ | SV |
| 27 | `shortint` | 105 | ✅ | SV |
| 28 | `int` | 106 | ✅ | SV |
| 29 | `longint` | 107 | ✅ | SV |
| 30 | `integer` | 108 | ✅ | Core |
| 31 | `time` | 109 | ✅ | Core |
| 32 | `real` | 110 | ✅ | Core |
| 33 | `realtime` | 111 | ✅ | Core |
| 34 | `shortreal` | 112 | ✅ | SV |
| 35 | `string` | 113 | ✅ | SV |
| 36 | `chandle` | 114 | ✅ | SV (DPI) |
| 37 | `event` | 115 | ✅ | Core |
| 38 | `signed` | 116 | ✅ | Core |
| 39 | `unsigned` | 117 | ✅ | Core |
| 40 | `const` | 118 | ✅ | SV |
| 41 | `var` | 119 | ✅ | SV |
| 42 | `ref` | 120 | ✅ | SV |
| 43 | `tri0` | 121 | ✅ | Core |
| 44 | `tri1` | 122 | ✅ | Core |
| 45 | `wand` | 123 | ✅ | Core |
| 46 | `wor` | 124 | ✅ | Core |
| 47 | `triand` | 125 | ✅ | Core |
| 48 | `trior` | 126 | ✅ | Core |
| 49 | `trireg` | 127 | ✅ | Core |
| 50 | `uwire` | 128 | ✅ | SV |
| 51 | `supply0` | 129 | ✅ | Core (M5) |
| 52 | `supply1` | 130 | ✅ | Core (M5) |
| 53 | `interconnect` | 131 | ✅ | SV (M5) |

**Expected:** 32/32 (already implemented)

---

## Category 3: Type System (7)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 54 | `parameter` | 200 | ✅ | Core |
| 55 | `localparam` | 201 | ✅ | Core |
| 56 | `typedef` | 202 | ✅ | SV |
| 57 | `struct` | 203 | ✅ | SV |
| 58 | `enum` | 204 | ✅ | SV |
| 59 | `union` | 205 | ✅ | SV |
| 60 | `tagged` | 206 | ✅ | SV |

**Expected:** 7/7 (already implemented)

---

## Category 4: Ports & Directions (4)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 61 | `input` | 300 | ✅ | Core |
| 62 | `output` | 301 | ✅ | Core |
| 63 | `inout` | 302 | ✅ | Core |
| 64 | `ref` | 120 | ✅ | SV (duplicate) |

**Expected:** 4/4 (already implemented)

---

## Category 5: Behavioral (14)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 65 | `always` | 400 | ✅ | Core |
| 66 | `always_comb` | 401 | ✅ | SV |
| 67 | `always_ff` | 402 | ✅ | SV |
| 68 | `always_latch` | 403 | ✅ | SV |
| 69 | `initial` | 404 | ✅ | Core |
| 70 | `final` | 405 | ✅ | SV |
| 71 | `begin` | 406 | ✅ | Core |
| 72 | `end` | 407 | ✅ | Core |
| 73 | `fork` | 408 | ✅ | Core |
| 74 | `join` | 409 | ✅ | Core |
| 75 | `join_any` | 410 | ✅ | SV |
| 76 | `join_none` | 411 | ✅ | SV |
| 77 | `automatic` | 412 | ✅ | SV |
| 78 | `static` | 413 | ✅ | SV |

**Expected:** 14/14 (already implemented)

---

## Category 6: Control Flow (17)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 79 | `if` | 500 | ? | Core |
| 80 | `else` | 501 | ? | Core |
| 81 | `case` | 502 | ? | Core |
| 82 | `casex` | 503 | ? | Core |
| 83 | `casez` | 504 | ? | Core |
| 84 | `endcase` | 505 | ? | Core |
| 85 | `default` | 506 | ? | Core |
| 86 | `for` | 507 | ? | Core |
| 87 | `while` | 508 | ? | Core |
| 88 | `repeat` | 509 | ? | Core |
| 89 | `foreach` | 510 | ? | SV |
| 90 | `do` | 511 | ? | SV |
| 91 | `break` | 512 | ? | SV |
| 92 | `continue` | 513 | ? | SV |
| 93 | `return` | 514 | ? | SV |
| 94 | `wait` | 515 | ? | Core |
| 95 | `wait_order` | 516 | ? | SV |

**Expected:** 17/17 (to verify)

---

## Category 7: Functions & Tasks (8)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 96 | `function` | 600 | ? | Core |
| 97 | `endfunction` | 601 | ? | Core |
| 98 | `task` | 602 | ? | Core |
| 99 | `endtask` | 603 | ? | Core |
| 100 | `void` | 604 | ? | SV |
| 101 | `return` | 514 | ? | SV (duplicate) |
| 102 | `pure` | 605 | ? | SV (DPI) |
| 103 | `context` | 606 | ? | SV (DPI) |

**Expected:** 8/8 (to verify)

---

## Category 8: Classes & OOP (15)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 104 | `class` | 700 | ? | SV |
| 105 | `endclass` | 701 | ? | SV |
| 106 | `extends` | 702 | ? | SV |
| 107 | `virtual` | 703 | ? | SV |
| 108 | `new` | 704 | ? | SV |
| 109 | `this` | 705 | ? | SV |
| 110 | `super` | 706 | ? | SV |
| 111 | `protected` | 707 | ? | SV |
| 112 | `local` | 708 | ? | SV |
| 113 | `extern` | 709 | ? | SV |
| 114 | `rand` | 710 | ? | SV |
| 115 | `randc` | 711 | ? | SV |
| 116 | `randomize` | 712 | ? | SV |
| 117 | `null` | 713 | ? | SV |
| 118 | `soft` | 714 | ? | SV |

**Expected:** 15/15 (to verify)

---

## Category 9: Constraints (10)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 119 | `constraint` | 800 | ? | SV |
| 120 | `solve` | 801 | ? | SV |
| 121 | `before` | 802 | ? | SV |
| 122 | `dist` | 803 | ? | SV |
| 123 | `inside` | 804 | ? | SV |
| 124 | `with` | 805 | ? | SV |
| 125 | `foreach` | 510 | ? | SV (duplicate) |
| 126 | `unique` | 806 | ? | SV |
| 127 | `unique0` | 807 | ? | SV (M9) |
| 128 | `soft` | 714 | ? | SV (duplicate) |

**Expected:** 10/10 (to verify)

---

## Category 10: Assertions (12)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 129 | `assert` | 900 | ? | SV |
| 130 | `assume` | 901 | ? | SV |
| 131 | `cover` | 902 | ? | SV |
| 132 | `expect` | 903 | ? | SV |
| 133 | `property` | 904 | ? | SV |
| 134 | `endproperty` | 905 | ? | SV |
| 135 | `sequence` | 906 | ? | SV |
| 136 | `endsequence` | 907 | ? | SV |
| 137 | `disable` | 908 | ? | Core |
| 138 | `iff` | 909 | ? | SV |
| 139 | `implies` | 910 | ✅ | SV (M5) |
| 140 | `restrict` | 911 | ? | SV |

**Expected:** 12/12 (to verify)

---

## Category 11: SVA Temporal Operators (18)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 141 | `eventually` | 1000 | ✅ | SV (M7) |
| 142 | `nexttime` | 1001 | ✅ | SV (M7) |
| 143 | `s_always` | 1002 | ✅ | SV (M7) |
| 144 | `s_eventually` | 1003 | ✅ | SV (M7) |
| 145 | `s_nexttime` | 1004 | ✅ | SV (M7) |
| 146 | `s_until` | 1005 | ✅ | SV (M5) |
| 147 | `s_until_with` | 1006 | ✅ | SV (M5) |
| 148 | `until` | 1007 | ✅ | SV (M5) |
| 149 | `until_with` | 1008 | ✅ | SV (M5) |
| 150 | `within` | 1009 | ✅ | SV (M5) |
| 151 | `accept_on` | 1010 | ✅ | SV (M7) |
| 152 | `reject_on` | 1011 | ✅ | SV (M7) |
| 153 | `sync_accept_on` | 1012 | ✅ | SV (M7) |
| 154 | `sync_reject_on` | 1013 | ✅ | SV (M7) |
| 155 | `throughout` | 1014 | ? | SV |
| 156 | `intersect` | 1015 | ? | SV |
| 157 | `first_match` | 1016 | ? | SV |
| 158 | `and` | 1017 | ? | SV (seq) |

**Expected:** 18/18 (14 done in M5/M7, verify remaining 4)

---

## Category 12: Coverage (7)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 159 | `covergroup` | 1100 | ? | SV |
| 160 | `endgroup` | 1101 | ? | SV |
| 161 | `coverpoint` | 1102 | ? | SV |
| 162 | `bins` | 1103 | ? | SV |
| 163 | `binsof` | 1104 | ? | SV |
| 164 | `cross` | 1105 | ? | SV |
| 165 | `iff` | 909 | ? | SV (duplicate) |

**Expected:** 7/7 (to verify)

---

## Category 13: Timing & Events (9)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 166 | `posedge` | 1200 | ? | Core |
| 167 | `negedge` | 1201 | ? | Core |
| 168 | `edge` | 1202 | ? | Core |
| 169 | `@` | - | - | Operator |
| 170 | `##` | - | - | Operator |
| 171 | `#` | - | - | Operator |
| 172 | `timeprecision` | 1203 | ? | SV |
| 173 | `timeunit` | 1204 | ? | SV |
| 174 | `realtime` | 111 | ✅ | Core (duplicate) |

**Expected:** 9/9 (to verify, 3 operators excluded)

---

## Category 14: Assignment & Force (6)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 175 | `assign` | 1300 | ? | Core |
| 176 | `deassign` | 1301 | ? | Core |
| 177 | `force` | 1302 | ? | Core |
| 178 | `release` | 1303 | ? | Core |
| 179 | `alias` | 1304 | ? | SV |
| 180 | `=` | - | - | Operator |

**Expected:** 6/6 (to verify, operator excluded)

---

## Category 15: DPI & Import/Export (6)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 181 | `import` | 1400 | ? | SV |
| 182 | `export` | 1401 | ? | SV (DPI) |
| 183 | `pure` | 605 | ? | SV (duplicate) |
| 184 | `context` | 606 | ? | SV (duplicate) |
| 185 | `chandle` | 114 | ✅ | SV (duplicate) |
| 186 | `forkjoin` | - | ? | SV |

**Expected:** 6/6 (to verify)

---

## Category 16: Primitives (20)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 187 | `and` | 1500 | ? | Core |
| 188 | `or` | 1501 | ? | Core |
| 189 | `nand` | 1502 | ? | Core |
| 190 | `nor` | 1503 | ? | Core |
| 191 | `xor` | 1504 | ? | Core |
| 192 | `xnor` | 1505 | ? | Core |
| 193 | `not` | 1506 | ? | Core |
| 194 | `buf` | 1507 | ? | Core |
| 195 | `bufif0` | 1508 | ? | Core |
| 196 | `bufif1` | 1509 | ? | Core |
| 197 | `notif0` | 1510 | ? | Core |
| 198 | `notif1` | 1511 | ? | Core |
| 199 | `nmos` | 1512 | ? | Core |
| 200 | `pmos` | 1513 | ? | Core |
| 201 | `cmos` | 1514 | ? | Core |
| 202 | `rnmos` | 1515 | ? | Core |
| 203 | `rpmos` | 1516 | ? | Core |
| 204 | `rcmos` | 1517 | ? | Core |
| 205 | `tran` | 1518 | ? | Core |
| 206 | `rtran` | 1519 | ? | Core |

**Expected:** 20/20 (to verify)

---

## Category 17: Qualifiers & Modifiers (22)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 207 | `priority` | 1600 | ? | SV |
| 208 | `unique` | 806 | ? | SV (duplicate) |
| 209 | `unique0` | 807 | ? | SV (duplicate) |
| 210 | `const` | 118 | ✅ | SV (duplicate) |
| 211 | `scalared` | 1601 | ✅ | Core (M4) |
| 212 | `vectored` | 1602 | ✅ | Core (M4) |
| 213 | `packed` | 1603 | ? | SV |
| 214 | `signed` | 116 | ✅ | Core (duplicate) |
| 215 | `unsigned` | 117 | ✅ | Core (duplicate) |
| 216 | `protected` | 707 | ? | SV (duplicate) |
| 217 | `local` | 708 | ? | SV (duplicate) |
| 218 | `static` | 413 | ✅ | SV (duplicate) |
| 219 | `automatic` | 412 | ✅ | SV (duplicate) |
| 220 | `virtual` | 703 | ? | SV (duplicate) |
| 221 | `wildcard` | 1604 | ✅ | SV (M3) |
| 222 | `matches` | 1605 | ⚠️ | SV (M3 95%) |
| 223 | `type` | 1606 | ✅ | SV (operator) |
| 224 | `var` | 119 | ✅ | SV (duplicate) |
| 225 | `ref` | 120 | ✅ | SV (duplicate) |
| 226 | `inout` | 302 | ✅ | Core (duplicate) |
| 227 | `let` | 1607 | ? | SV |
| 228 | `untyped` | 1608 | ✅ | SV (M9) |

**Expected:** 22/22 (to verify, many duplicates)

---

## Category 18: Drive & Net Strengths (14)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 229 | `strong0` | 1700 | ✅ | Core (M6) |
| 230 | `strong1` | 1701 | ✅ | Core (M6) |
| 231 | `weak0` | 1702 | ✅ | Core (M6) |
| 232 | `weak1` | 1703 | ✅ | Core (M6) |
| 233 | `pull0` | 1704 | ✅ | Core (M6) |
| 234 | `pull1` | 1705 | ✅ | Core (M6) |
| 235 | `highz0` | 1706 | ✅ | Core (M4) |
| 236 | `highz1` | 1707 | ✅ | Core (M4) |
| 237 | `small` | 1708 | ✅ | Core (M4) |
| 238 | `medium` | 1709 | ✅ | Core (M4) |
| 239 | `large` | 1710 | ✅ | Core (M4) |
| 240 | `supply0` | 129 | ✅ | Core (duplicate) |
| 241 | `supply1` | 130 | ✅ | Core (duplicate) |
| 242 | `tri` | 1711 | ? | Core |

**Expected:** 14/14 (11 done in M4/M6, verify remaining 3)

---

## Category 19: Configuration & Advanced (12)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 243 | `config` | 1800 | ✅ | SV (M8) |
| 244 | `endconfig` | 1801 | ✅ | SV (M8) |
| 245 | `design` | 1802 | ✅ | SV (M8) |
| 246 | `instance` | 1803 | ✅ | SV (M8) |
| 247 | `liblist` | 1804 | ✅ | SV (M8) |
| 248 | `library` | 1805 | ✅ | SV (M8) |
| 249 | `use` | 1806 | ✅ | SV (M8) |
| 250 | `cell` | 1807 | ✅ | SV (M8) |
| 251 | `showcancelled` | 1808 | ✅ | Core (M9) |
| 252 | `noshowcancelled` | 1809 | ✅ | Core (M9) |
| 253 | `pulsestyle_onevent` | 1810 | ✅ | Core (M9) |
| 254 | `pulsestyle_ondetect` | 1811 | ✅ | Core (M9) |

**Expected:** 12/12 (done in M8/M9)

---

## Category 20: Miscellaneous (10)

| # | Keyword | Test # | Status | Notes |
|---|---------|--------|--------|-------|
| 255 | `randsequence` | 1900 | ✅ | SV (M9) |
| 256 | `endsequence` | 907 | ✅ | SV (duplicate) |
| 257 | `bind` | 1901 | ✅ | SV (M5) |
| 258 | `defparam` | 1902 | ? | Core |
| 259 | `specparam` | 1903 | ? | Core |
| 260 | `genvar` | 1904 | ? | SV |
| 261 | `pullup` | 1905 | ? | Core |
| 262 | `pulldown` | 1906 | ? | Core |
| 263 | `global` | 1907 | ? | SV |
| 264 | `forkjoin` | 1908 | ? | SV |

**Expected:** 10/10 (to verify)

---

## Summary Statistics

| Category | Total | Verified ✅ | To Verify ? | Failed ❌ |
|----------|-------|-------------|-------------|-----------|
| Structural | 21 | 21 | 0 | 0 |
| Data Types | 32 | 32 | 0 | 0 |
| Type System | 7 | 7 | 0 | 0 |
| Ports | 4 | 4 | 0 | 0 |
| Behavioral | 14 | 14 | 0 | 0 |
| Control Flow | 17 | 0 | 17 | 0 |
| Functions | 8 | 0 | 8 | 0 |
| Classes | 15 | 0 | 15 | 0 |
| Constraints | 10 | 0 | 10 | 0 |
| Assertions | 12 | 1 | 11 | 0 |
| SVA Temporal | 18 | 14 | 4 | 0 |
| Coverage | 7 | 0 | 7 | 0 |
| Timing | 9 | 1 | 8 | 0 |
| Assignment | 6 | 0 | 6 | 0 |
| DPI | 6 | 1 | 5 | 0 |
| Primitives | 20 | 0 | 20 | 0 |
| Qualifiers | 22 | 10 | 11 | 1 |
| Drive Strengths | 14 | 11 | 3 | 0 |
| Config | 12 | 12 | 0 | 0 |
| Misc | 10 | 2 | 8 | 0 |
| **TOTAL** | **264** | **130** | **133** | **1** |

**Note:** Total is 264 due to duplicates. Unique keywords = 243.

**Current Coverage:** 130/243 verified (53.5%)  
**To Verify:** 113 keywords (46.5%)  
**Known Limitation:** 1 keyword (`matches` in expressions)

---

## Implementation Strategy

### Phase 2.1: Write All Tests (Days 4-5)
- Complete `verilog-parser-lrm-complete_test.cc` with all 243 keywords
- Organize by category for maintainability
- Use minimal syntax for each test

### Phase 2.2: Run & Triage (Day 6)
- Run: `bazel test //verible/verilog/parser:verilog-parser-lrm-complete_test`
- Categorize results:
  - ✅ Already passing
  - ❌ Failing - token missing
  - ❌ Failing - grammar missing
  - ⚠️ Syntax error in test

### Phase 2.3: Fix Failures (Days 7-10)
- Fix lexer for missing tokens
- Add grammar rules for missing keywords
- Fix incorrect test syntax
- Re-test until 100% pass

### Phase 2.4: Expand Coverage (Days 11-12)
- Add complex test cases
- Test keyword combinations
- Real-world scenarios
- Target: 300+ total tests

---

## Success Metrics

**Must Achieve:**
- 240+/243 keywords passing (98%+)
- All high-priority categories at 100%
- Zero regressions

**Stretch Goal:**
- 243/243 keywords (100%)
- 350+ comprehensive tests
- Sub-second test execution

