# Unity GUID System & Asset References

## Overview

Unity uses a GUID-based system to track asset references. Every asset has a `.meta` file containing a unique 32-character hexadecimal GUID, import settings, and asset configuration.

## Critical Rules

1. **Never manually create GUIDs** - always copy from existing `.meta` files
2. **Keep `.meta` files in version control** - they're essential for maintaining references
3. **Delete files via Unity Editor** - or manually delete both `.cs` and `.meta` together
4. **GUID format**: Exactly 32 hexadecimal characters (0-9, a-f only)

## Valid vs Invalid GUIDs

**Valid GUID**: `6004172616168c346951d6f4cddd83da` (32 hex characters)
**Invalid GUID**: `a1b2c3d4e5f6g7h8i9j0k1l2m3n4o5p6` (contains non-hex: g, h, i, j, k, l, m, n, o, p)

## Finding the Correct GUID

```bash
# Find a script's GUID
grep "^guid:" Assets/Scripts/YourScript.cs.meta

# Find all invalid GUIDs
grep -Ern "guid: [^0-9a-f]" Assets/

# Find orphaned meta files
for meta in Assets/**/*.meta; do
    [ -f "${meta%.meta}" ] || echo "Orphaned: $meta"
done
```

## Common GUID Errors

### Error: GUID Extraction Failed

**Error Message**:
```
Could not extract GUID in text file Assets/Prefabs/MyPrefab.prefab at line 97.
```

**Root Cause**: Invalid or malformed GUID in prefab's MonoBehaviour reference

**Location Example**:
```yaml
m_Script: {fileID: 11500000, guid: a1b2c3d4e5f6g7h8i9j0k1l2m3n4o5p6, type: 3}
```

**Solution**:
1. Find the script's `.meta` file
```bash
find Assets/Scripts -name "MyScript.cs"
grep "^guid:" Assets/Scripts/MyScript.cs.meta
```

2. Copy the correct GUID from the meta file

3. Replace in prefab:
```yaml
m_Script: {fileID: 11500000, guid: 6004172616168c346951d6f4cddd83da, type: 3}
```

### Error: Broken PPtr

**Error Message**:
```
Broken PPtr [guid] in file [path]
```

**Root Cause**: Orphaned `.meta` files for deleted scripts

**How It Happens**:
- Script deleted outside Unity Editor
- `.meta` file still exists in git
- Unity can't find the asset but meta file references it

**Solution**:
```bash
# Find orphaned meta files
git status | grep -E "D.*\.cs$" -A 1

# Remove orphaned meta files
git rm path/to/deleted/file.cs.meta
```

## Git Workflow with Meta Files

### File Patterns
```
Asset.ext           # The actual asset
Asset.ext.meta      # Unity metadata (GUID, import settings)
```

**Always keep them synchronized!**

### When Adding New Assets

```
Create Asset → Via Unity Editor? → Unity handles .meta
                    ↓
               Verify in git status
                    ↓
            Commit both files together
```

**Manual creation** (if not using Unity Editor):
1. Create the asset file
2. Let Unity generate `.meta` file
3. Stage both files: `git add Asset.ext Asset.ext.meta`
4. Commit together

### When Deleting Assets

```
Delete Asset → Via Unity Editor? → Unity deletes both
                      ↓
               Check git status
                      ↓
              Commit deletions
```

**Manual deletion**:
```bash
# Delete both files
rm Assets/Scripts/MyScript.cs
rm Assets/Scripts/MyScript.cs.meta

# Stage deletions
git add -A

# Or explicitly
git rm Assets/Scripts/MyScript.cs
git rm Assets/Scripts/MyScript.cs.meta
```

### Checking for Issues

```bash
# Check for orphaned meta files before commit
for meta in Assets/**/*.meta; do
    [ -f "${meta%.meta}" ] || echo "Orphaned: $meta"
done

# Find untracked meta files
git status | grep "\.meta$"

# Verify all .cs files have matching .meta files
find Assets -name "*.cs" | while read file; do
    [ -f "$file.meta" ] || echo "Missing .meta: $file"
done
```

## Prefab References

### How Prefabs Reference Scripts

Prefabs store script references using GUIDs from `.meta` files:

```yaml
MonoBehaviour:
  m_Script: {fileID: 11500000, guid: 6004172616168c346951d6f4cddd83da, type: 3}
```

Where:
- `fileID: 11500000` = MonoScript asset type (always this value)
- `guid: ...` = The script's GUID from its `.meta` file
- `type: 3` = Asset type indicator

### When Creating Prefabs Manually

**Best Practice**: Always use Unity Editor to create prefabs

**If editing manually**:
1. Find the script you want to reference
2. Open its `.meta` file
3. Copy the GUID
4. Use in prefab with correct format

### Validating Prefab GUIDs

```bash
# Extract all GUIDs from a prefab
grep "guid:" Assets/Prefabs/MyPrefab.prefab

# Check if all GUIDs are valid hex
grep "guid:" Assets/Prefabs/MyPrefab.prefab | grep -E "guid: [^0-9a-f]"

# Find the script file for a specific GUID
guid="6004172616168c346951d6f4cddd83da"
find Assets -name "*.meta" -exec grep -l "guid: $guid" {} \;
```

## Scene References

Scenes also use GUIDs to reference assets. Same rules apply:

```yaml
--- !u!1 &1234567890
GameObject:
  m_Component:
  - component: {fileID: 1234567891}
  - component: {fileID: 1234567892, guid: 6004172616168c346951d6f4cddd83da, type: 3}
```

## Best Practices

### Do's
✅ Use Unity Editor for all asset operations
✅ Keep `.meta` files in version control
✅ Commit `.cs` and `.meta` files together
✅ Delete through Unity Editor
✅ Copy GUIDs from existing `.meta` files
✅ Validate GUID format before using

### Don'ts
❌ Manually create or edit GUIDs
❌ Delete only `.cs` without `.meta`
❌ Delete only `.meta` without `.cs`
❌ Edit prefabs/scenes without Unity Editor
❌ Ignore orphaned `.meta` files
❌ Use non-hexadecimal characters in GUIDs

## Troubleshooting Commands

```bash
# Find all assets missing meta files
find Assets -type f ! -name "*.meta" ! -path "*/.*" | while read file; do
    [ -f "$file.meta" ] || echo "Missing .meta: $file"
done

# Find all meta files without matching assets
find Assets -name "*.meta" | while read meta; do
    asset="${meta%.meta}"
    [ -f "$asset" ] || echo "Orphaned: $meta"
done

# Validate all GUIDs are proper hex
find Assets -name "*.meta" -exec grep -H "guid:" {} \; | grep -v "guid: [0-9a-f]\{32\}"

# List all GUIDs in project
find Assets -name "*.meta" -exec grep "guid:" {} \; | sort | uniq

# Find duplicate GUIDs (should never happen!)
find Assets -name "*.meta" -exec grep "guid:" {} \; | sort | uniq -d
```

## Recovery Strategies

### If GUID References Break

1. **Identify broken references**:
   - Unity Console shows "Missing Referenced Script"
   - Prefabs/scenes show "None (Script)" in Inspector

2. **Find the original script**:
   - Search project for script name
   - Check if script was renamed or moved

3. **Fix the reference**:
   - Reassign in Unity Inspector (automatic GUID fix)
   - Or manually copy correct GUID to prefab/scene file

### If Meta Files Are Lost

1. **Never delete `.meta` files from version control**
2. If already deleted:
   - Unity generates new GUIDs (breaks all references!)
   - May need to restore from backup
   - Or manually reassign all references in Unity Editor

### Mass Reference Fixing

If many references break (e.g., after bad merge):
1. Create a backup
2. Use Unity's "Reimport All" (risky, regenerates meta files)
3. Manually fix critical prefabs in Inspector
4. Use git to restore known-good `.meta` files

## Additional Resources

- Unity Manual: [Meta File Format](https://docs.unity3d.com/Manual/AssetMetaFiles.html)
- Unity Manual: [Asset Database](https://docs.unity3d.com/Manual/AssetDatabase.html)
- Unity Forum: Search "GUID extraction error"
