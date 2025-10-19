# Changelog

All notable changes to Verible will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

---

## [5.3.0] - 2025-10-19

### Added
- **Deep Nesting Macro Propagation**: Macros from deeply nested includes (3+ levels) now correctly propagate to parent files
- **UVM Library Integration**: Added UVM-Core 2020.3.1 (IEEE 1800.2-2017) as git submodule at `third_party/uvm/`
- **Enhanced UVM Macro Registry**: Added 4 new macros (`uvm_object_new`, `DV_COMMON_CLK_CONSTRAINT`, `gmv`, `DV_MUBI8_DIST`)
- **Include File Support**: Full `include` directive resolution with search paths
- **IncludeFileResolver Class**: New class for managing include paths and file caching
- **`--include_paths` Flag**: Command-line flag for specifying include directories
- **`--preprocess` Flag**: Command-line flag to enable/disable preprocessing

### Fixed
- **Critical**: Deep nesting macro propagation bug - macros from child preprocessors now correctly merge back to parent
- **Critical**: `expand_macros` configuration no longer incorrectly tied to `include_paths`
- Macro definitions now correctly inherit parent preprocessor context

### Changed
- None - all changes are backward compatible

### Validation
- **Test Results**: 136/136 tests passing (100%)
  - 124 UVM parser tests
  - 2 deep nesting tests
  - 10 include file tests
- **OpenTitan Validation**: 2,094/2,108 files (99.3% success rate)
- **Performance**: Zero overhead - baseline performance maintained

### Documentation
- Added `UVM_CAPABILITIES_REALITY.md` - Complete UVM feature documentation
- Updated `VERIPG_INTEGRATION_GUIDE.md` - Added UVM testbench analysis section
- Added `VERIPG_UVM_USAGE_EXAMPLES.md` - Practical UVM integration examples
- Added `OPENTITAN_PARSING_ANALYSIS.md` - OpenTitan corpus analysis
- Updated `RELEASE_NOTES_v5.3.0.md` - Comprehensive release documentation

### Breaking Changes
- None ✅

---

## [5.2.0] - 2025-01-18

### Added
- Kythe variable reference extraction in `verible-verilog-semantic`
- JSON output schema v1.1.0 with Kythe facts
- `--include_kythe` flag for enabling Kythe extraction

### Fixed
- Various Kythe extraction edge cases

---

## [5.1.0] - Previous Release

### Added
- Initial semantic analysis features
- Various parser improvements

---

## [5.0.0] - Baseline

Initial fork/baseline version.

---

## Legend

- **Added**: New features
- **Changed**: Changes in existing functionality  
- **Deprecated**: Soon-to-be removed features
- **Removed**: Removed features
- **Fixed**: Bug fixes
- **Security**: Vulnerability fixes

---

**Repository**: https://github.com/chipsalliance/verible  
**Fork**: https://github.com/[your-username]/verible

