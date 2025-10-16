# GitHub Release Creation Instructions
## How to Publish v5.0.0 on GitHub

**Status**: Tag v5.0.0 pushed to GitHub ✅  
**Next**: Create GitHub Release (manual or CLI)

---

## 📋 Release Information

**Version**: v5.0.0  
**Tag**: v5.0.0 (already pushed)  
**Repository**: https://github.com/semiconductor-designs/verible  
**Title**: VeriPG Validator v5.0.0 - Production Ready

---

## 🎯 Option A: GitHub Web UI (Recommended for First Release)

### Step 1: Navigate to Releases
1. Go to https://github.com/semiconductor-designs/verible
2. Click on "Releases" (right sidebar or `/releases`)
3. Click "Draft a new release"

### Step 2: Fill Release Form

**Choose a tag**: Select `v5.0.0` from dropdown (already exists)

**Release title**: 
```
VeriPG Validator v5.0.0 - Production Ready
```

**Description**: Copy from `GITHUB_RELEASE_NOTES_v5.0.0.md` (see below)

**Attach binaries**:
- Upload `release/veripg-validator-v5.0.0-macOS-arm64.tar.gz`
- Upload `release/veripg-validator-v5.0.0-macOS-arm64.zip`
- Upload `release/release-checksums.txt`

**Options**:
- ✅ Set as the latest release
- ⬜ Set as a pre-release (NO - this is production)
- ⬜ Create a discussion for this release (optional)

### Step 3: Publish
Click "Publish release"

---

## 🎯 Option B: GitHub CLI (Faster)

### Prerequisites
```bash
# Install GitHub CLI if not already installed
brew install gh

# Authenticate
gh auth login
```

### Create Release
```bash
cd /Users/jonguksong/Projects/verible

# Create release with notes
gh release create v5.0.0 \
  --title "VeriPG Validator v5.0.0 - Production Ready" \
  --notes-file GITHUB_RELEASE_NOTES_v5.0.0.md \
  release/veripg-validator-v5.0.0-macOS-arm64.tar.gz \
  release/veripg-validator-v5.0.0-macOS-arm64.zip \
  release/release-checksums.txt
```

### Verify Release
```bash
gh release view v5.0.0
```

---

## 🎯 Option C: GitHub API (Advanced)

```bash
# Get release notes content
NOTES=$(cat GITHUB_RELEASE_NOTES_v5.0.0.md)

# Create release
curl -X POST \
  -H "Accept: application/vnd.github+json" \
  -H "Authorization: Bearer YOUR_GITHUB_TOKEN" \
  https://api.github.com/repos/semiconductor-designs/verible/releases \
  -d "{
    \"tag_name\": \"v5.0.0\",
    \"name\": \"VeriPG Validator v5.0.0 - Production Ready\",
    \"body\": \"$NOTES\",
    \"draft\": false,
    \"prerelease\": false
  }"

# Upload assets (requires release_id from previous response)
# ... (complex, use gh CLI instead)
```

---

## 📄 Release Notes Content

**File**: `GITHUB_RELEASE_NOTES_v5.0.0.md` (created separately)

The release notes have been prepared in a separate file optimized for GitHub's markdown rendering.

---

## ✅ Post-Release Checklist

After publishing:
1. ✅ Verify release is visible at https://github.com/semiconductor-designs/verible/releases
2. ✅ Verify assets (tar.gz, zip, checksums) are downloadable
3. ✅ Verify release notes render correctly
4. ✅ Test download and extraction
5. ✅ Update project README to reference v5.0.0
6. ✅ Announce to VeriPG team (Phase 7)

---

## 🔗 Quick Links

**Repository**: https://github.com/semiconductor-designs/verible  
**Releases**: https://github.com/semiconductor-designs/verible/releases  
**Tag**: https://github.com/semiconductor-designs/verible/releases/tag/v5.0.0

---

*Created: January 16, 2025*

