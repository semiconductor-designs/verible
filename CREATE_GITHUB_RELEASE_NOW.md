# Create GitHub Release v5.0.0 - Step by Step Guide
## Follow These Steps Now

**Status**: Git tag v5.0.0 is already pushed ✅  
**Assets**: Ready in `release/` directory ✅  
**Release Notes**: Prepared and ready ✅

---

## 📋 Step-by-Step Instructions

### Step 1: Open GitHub Releases Page

**Click this link**: https://github.com/semiconductor-designs/verible/releases/new?tag=v5.0.0

OR manually:
1. Go to: https://github.com/semiconductor-designs/verible
2. Click "Releases" (right sidebar)
3. Click "Draft a new release" button
4. Select tag: **v5.0.0** (should be in dropdown)

---

### Step 2: Fill in Release Details

**Release Title** (copy this):
```
VeriPG Validator v5.0.0 - Production Ready
```

**Description** (copy from file):
Open `GITHUB_RELEASE_NOTES_v5.0.0.md` and copy the entire contents into the description box.

Quick copy command:
```bash
cat GITHUB_RELEASE_NOTES_v5.0.0.md | pbcopy
```
(Then paste into GitHub description box)

---

### Step 3: Upload Release Assets

Click "Attach binaries by dropping them here or selecting them"

Upload these 3 files from the `release/` directory:

1. ✅ **veripg-validator-v5.0.0-macOS-arm64.tar.gz** (603KB)
   - Location: `release/veripg-validator-v5.0.0-macOS-arm64.tar.gz`

2. ✅ **veripg-validator-v5.0.0-macOS-arm64.zip** (611KB)
   - Location: `release/veripg-validator-v5.0.0-macOS-arm64.zip`

3. ✅ **release-checksums.txt**
   - Location: `release/release-checksums.txt`

---

### Step 4: Configure Release Options

**Check these settings**:
- ✅ **Set as the latest release** (CHECK THIS)
- ⬜ **Set as a pre-release** (LEAVE UNCHECKED)
- ⬜ **Create a discussion for this release** (OPTIONAL - your choice)

---

### Step 5: Publish Release

Click the big green **"Publish release"** button

---

## ✅ Verification

After publishing, verify:

1. **Release is visible**: https://github.com/semiconductor-designs/verible/releases/tag/v5.0.0
2. **Assets are downloadable** (3 files)
3. **Release notes display correctly**
4. **"Latest release" badge shows v5.0.0**

---

## 🎉 Done!

Once published, the release will be:
- ✅ Publicly visible
- ✅ Listed as latest release
- ✅ Assets downloadable by anyone
- ✅ Indexed by GitHub

---

## 📱 Quick Command Reference

```bash
# Copy release notes to clipboard (macOS)
cd /Users/jonguksong/Projects/verible
cat GITHUB_RELEASE_NOTES_v5.0.0.md | pbcopy

# View release assets
ls -lh release/veripg-validator-v5.0.0-*

# View checksums
cat release/release-checksums.txt
```

---

**Ready?** Open the link and follow the steps! 🚀

https://github.com/semiconductor-designs/verible/releases/new?tag=v5.0.0

