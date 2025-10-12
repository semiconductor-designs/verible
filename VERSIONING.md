# Verible Versioning Scheme

**Standard:** Semantic Versioning (SemVer)  
**Format:** `vMAJOR.MINOR.PATCH`  
**Current Version:** `v2.0.0`

---

## Version Format

```
v2.0.0
│ │ │
│ │ └─ PATCH: Bug fixes (backward compatible)
│ └─── MINOR: New features (backward compatible)
└───── MAJOR: Breaking changes
```

---

## Version History

| Version | Date | Description |
|---------|------|-------------|
| **v2.0.0** | Oct 12, 2025 | **Current Release** - Major enhancements over base Verible |
| v1.x.x | - | Base Verible (upstream chipsalliance) |

---

## v2.0.0 Release (Current)

**Major Changes:**
- ✅ Phase A: Type resolution metadata
- ✅ Phase B: Cross-reference metadata
- ✅ Phase C: Scope/hierarchy metadata
- ✅ Phase D: Dataflow metadata
- ✅ Fixed: MOS/switch gate CST bug (12 tests)
- ✅ Fixed: UDP initial statement bug (20 tests)

**Test Results:** 948/949 passing (99.9%)  
**Status:** Production Ready

---

## Future Versioning Rules

### When to Increment MAJOR (v3.0.0, v4.0.0, ...)

Increment when making **incompatible/breaking changes**:
- Changes to JSON metadata structure that break existing parsers
- Grammar changes that reject previously valid code
- Removal of deprecated features
- API/interface changes

**Example:**
```bash
git tag -a v3.0.0 -m "Breaking change: New CST node structure"
```

### When to Increment MINOR (v2.1.0, v2.2.0, ...)

Increment when adding **new features** (backward compatible):
- New metadata fields (additive only)
- New grammar support (enables new constructs)
- Performance improvements
- New CST node types

**Example:**
```bash
git tag -a v2.1.0 -m "Added: Interface metadata support"
```

### When to Increment PATCH (v2.0.1, v2.0.2, ...)

Increment when making **bug fixes** (backward compatible):
- Parser bug fixes
- Crash fixes
- Memory leak fixes
- Documentation corrections

**Example:**
```bash
git tag -a v2.0.1 -m "Fixed: Parser crash on nested packages"
```

---

## Release Process

### 1. Decide Version Number

Based on changes:
- Breaking change? → Increment MAJOR
- New feature? → Increment MINOR
- Bug fix only? → Increment PATCH

### 2. Create Tag

```bash
cd /Users/jonguksong/Projects/verible
git tag -a v2.1.0 -m "Release v2.1.0: Brief description

Detailed changes:
- Feature 1
- Feature 2
- Bug fix 3

Test results: X/Y passing
Status: Production Ready"
```

### 3. Push Tag

```bash
git push origin v2.1.0
```

### 4. Update Documentation

Update `VERSIONING.md` with new version in history table.

---

## Examples of Future Releases

### Bug Fix Release (v2.0.1)
```
Fixed: Parser crash on deeply nested expressions
Fixed: Memory leak in CST builder
Test results: 949/949 passing (100%)
```

### Feature Release (v2.1.0)
```
Added: Interface metadata extraction
Added: Program block support
Enhanced: Better error messages
Test results: 965/965 passing
```

### Breaking Change Release (v3.0.0)
```
Breaking: New JSON schema version
Breaking: Deprecated fields removed
Added: Unified metadata structure
Migration guide: See MIGRATION_v2_to_v3.md
```

---

## Tag Naming Convention

### ✅ Correct (Use These)

- `v2.0.0` - Major release
- `v2.1.0` - Minor release (new features)
- `v2.0.1` - Patch release (bug fixes)
- `v2.1.5` - Multiple patches on minor version
- `v3.0.0-beta.1` - Pre-release (optional)

### ❌ Incorrect (Don't Use)

- `veripg-phases-9-22-v1.0` - Too verbose
- `v2.0` - Missing patch number
- `2.0.0` - Missing 'v' prefix
- `v2.0.0-final` - Redundant suffix
- `release-2.0.0` - Wrong prefix

---

## Pre-release Versions (Optional)

For testing before official release:

```bash
v2.1.0-alpha.1    # Very early testing
v2.1.0-beta.1     # Feature complete, testing
v2.1.0-rc.1       # Release candidate
v2.1.0            # Official release
```

**Usage:**
```bash
git tag -a v2.1.0-beta.1 -m "Beta release for testing"
```

---

## Checking Current Version

```bash
# Show latest tag
git describe --tags --abbrev=0

# Show all versions
git tag -l "v*" | sort -V

# Show version with commit count
git describe --tags
```

---

## Migration from Old Tags

**Old tags** (deprecated, kept for history):
- `veripg-phases-9-22-v1.0`
- `veripg-phases-9-22-v1.1`
- `veripg-phases-9-22-v1.2`
- `veripg-phases-abcd-v1.0`
- `veripg-all-issues-fixed-v1.0`

**New standard:** Use only `vX.Y.Z` format going forward.

**Note:** Old tags are kept for historical reference but should not be used for new releases.

---

## Summary

✅ **Use:** Semantic Versioning (vMAJOR.MINOR.PATCH)  
✅ **Current:** v2.0.0  
✅ **Next bug fix:** v2.0.1  
✅ **Next feature:** v2.1.0  
✅ **Next breaking change:** v3.0.0

**Simple, clean, industry standard!** 🚀

