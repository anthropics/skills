---
name: safe-editing
description: "Safe strategies for multi-edit and multi-file code modifications. Use this skill WHENEVER you need to make more than 3 edits to a single file, edit multiple files in sequence, perform batch find-and-replace operations, or refactor code across a codebase. This skill prevents common failure modes: str_replace failing on non-unique strings, cascade failures where early edits break later search strings, encoding mismatches with unicode characters, and half-edited files with no rollback. Trigger for: refactoring, bulk edits, config changes across files, any task where you think 'I need to make a lot of small changes'. Even for seemingly simple multi-edit tasks — use it. The failure rate on 10+ sequential str_replace calls without a strategy is surprisingly high."
---

# Safe Editing Skill

## The Problem

The `str_replace` tool requires exact, unique string matches. This creates compounding failure modes when making multiple edits:

1. **Non-unique matches**: The search string appears more than once. The tool refuses. You add more context, guess wrong, waste a round-trip.
2. **Cascade failures**: Edit 5 changes content near edit 17's search string. Edit 17 now fails because its context shifted.
3. **Encoding ghosts**: Unicode characters that look identical render differently (`é` vs `\u00E9`, `—` vs `--`, smart quotes vs straight quotes). The replace silently fails.
4. **No rollback**: If edit 15 of 30 fails, edits 1-14 are already applied. The file is in an inconsistent half-edited state.
5. **Context drift**: In long conversations, your mental model of the file diverges from its actual state after multiple edits.

## Strategy Selection

Before editing, choose the right strategy based on the task:

### Few edits (1-3) → Direct str_replace
Just do it. Check each one succeeded. No special strategy needed.

### Several related edits (4-10) → Batch script
Write a Python or sed script that applies all changes in one pass. This eliminates cascade failures because the script sees the original file.

### Many edits (10+) → Full rewrite of section
If you're changing more than 10 things in a file, it's often safer and faster to rewrite the affected section or the entire file. Use `create_file` to write the new version, or use a script that reads the original, transforms it, and writes the result.

### Cross-file edits → Script with verification
Write a script that edits all files and verifies each change. Include a dry-run mode.

## Core Principles

### 1. Read before you edit
ALWAYS `view` the file (or the relevant line range) immediately before editing. Never rely on your memory of what the file contains, especially after previous edits in the same conversation. Your mental model drifts.

```
# GOOD: View first, edit second
view file.py lines 45-60
str_replace in file.py

# BAD: Edit from memory
str_replace in file.py  ← might fail, content may have changed
```

### 2. One conceptual change per str_replace
Don't try to be clever with large multi-line replacements that change several things at once. Each str_replace should do one thing. This makes failures easy to diagnose.

### 3. Use unique anchors
When the string you want to replace isn't unique, include surrounding context as your search string — but choose context that IS unique:

```
# BAD: Too common, probably appears multiple times
old_str: "return result"

# BETTER: Include the function signature as anchor
old_str: "def process_data(items):\n    result = []\n    return result"

# BEST: Include a unique comment or nearby unique identifier
old_str: "# Process the quarterly data\n    return result"
```

### 4. For batch edits: Python script in one pass
When you need 5+ related edits, write a Python script:

```python
with open('target.py', 'r') as f:
    content = f.read()

# All replacements defined upfront
replacements = [
    ('old_string_1', 'new_string_1'),
    ('old_string_2', 'new_string_2'),
    # ... all changes
]

for old, new in replacements:
    if old in content:
        content = content.replace(old, new)
        print(f"Fixed: {new[:50]}...")
    else:
        print(f"NOT FOUND: {old[:50]}...")

with open('target.py', 'w') as f:
    f.write(content)
```

This approach:
- Applies all changes to the original content (no cascade)
- Reports what succeeded and what failed
- Can be re-run safely
- Is auditable — you can see all changes in one place

### 5. Handle unicode explicitly
When editing files with non-ASCII characters, ALWAYS view the raw file first to check the actual encoding:

```bash
# Check for unicode escapes vs literal characters
grep -n "é\|ë\|ö\|ü\|à" file.js
# Check hex representation
hexdump -C file.js | grep -i "c3 a9"  # é in UTF-8
```

Common traps:
- JavaScript source may use `\u00E9` while the rendered text shows `é`
- Smart quotes `""` vs straight quotes `""`
- Em-dash `—` vs double hyphen `--`
- Non-breaking space ` ` vs regular space ` `

When in doubt, copy the exact bytes from the view output rather than typing the character yourself.

### 6. Verify after editing
After completing your edits, verify the file is correct:

```bash
# For code: try to parse/compile it
python -c "import ast; ast.parse(open('file.py').read())"
node --check file.js

# For any file: check the edited lines
view file.py lines 40-60

# For multiple edits: diff against expected
diff original.py edited.py
```

### 7. Backup before bulk edits
For risky operations on important files:

```bash
cp important_file.py important_file.py.bak
# ... make edits ...
# If things go wrong:
cp important_file.py.bak important_file.py
```

## Common Patterns

### Pattern: Config value updates across files
```bash
# Find all files containing the old value
grep -rn "old_api_url" --include="*.py" .

# Script to replace in all files
find . -name "*.py" -exec sed -i 's|old_api_url|new_api_url|g' {} +

# Verify
grep -rn "old_api_url" --include="*.py" .  # should return nothing
grep -rn "new_api_url" --include="*.py" .  # should show all replacements
```

### Pattern: Rename a function/variable across a project
```bash
# First: find all occurrences to understand scope
grep -rn "oldFunctionName" --include="*.ts" .

# Check it's safe (not a substring of something else)
grep -rn "oldFunctionName" --include="*.ts" . | grep -v "oldFunctionNameExact"

# Apply with word boundaries
find . -name "*.ts" -exec sed -i 's/\boldFunctionName\b/newFunctionName/g' {} +
```

### Pattern: Multiple edits to one section of a file
Instead of 5 str_replace calls on nearby lines, extract the section, edit it as a whole, and replace the entire section:

```
# 1. View the section
view file.py lines 100-150

# 2. Replace the entire section in one str_replace
str_replace:
  old_str: [lines 100-150 as one block]
  new_str: [the whole rewritten section]
```

This is one operation instead of five, with one failure point instead of five.

### Pattern: Large-scale text rewriting (like the typography fixes)
When rewriting many text strings (as in document generation):

```python
# Define all fixes as a dictionary
fixes = {
    'Original text that needs fixing': 'Improved version of the text',
    'Another line to change': 'Better version',
    # ... can be 50+ entries
}

# Apply in one pass
with open('generator.js', 'r') as f:
    content = f.read()

fixed = 0
not_found = 0
for old, new in fixes.items():
    if old in content:
        content = content.replace(old, new)
        fixed += 1
    else:
        not_found += 1
        print(f"NOT FOUND: {old[:60]}...")

with open('generator.js', 'w') as f:
    f.write(content)

print(f"Fixed: {fixed}, Not found: {not_found}")
```

## Decision Flowchart

```
How many edits do I need to make?
│
├─ 1-3 edits
│  └─ Use str_replace directly
│     └─ View the target lines first
│
├─ 4-10 edits in one file
│  └─ Are they in the same section?
│     ├─ Yes → Replace the whole section in one str_replace
│     └─ No → Write a Python batch script
│
├─ 10+ edits in one file
│  └─ Is it a rewrite or targeted fixes?
│     ├─ Rewrite → Regenerate the file with create_file
│     └─ Targeted → Python batch script with verification
│
└─ Edits across multiple files
   └─ Write a script with:
      ├─ grep to find all targets
      ├─ sed or python to apply changes
      └─ grep to verify results
```

## Anti-patterns (what NOT to do)

1. **Don't chain 20 str_replace calls** hoping they'll all work. After the 5th one, your context is stale and failures compound.

2. **Don't type unicode characters from memory**. Copy them from the file view.

3. **Don't edit a file you haven't viewed in this conversation turn**. Always re-read first.

4. **Don't make the old_str too short**. `"return x"` matches everywhere. Be specific.

5. **Don't make the old_str too long**. 30+ lines of context is fragile — any whitespace difference causes failure. Find the sweet spot: enough to be unique, short enough to be exact.

6. **Don't ignore str_replace failures**. If it says "not found", STOP. View the file. Understand why. Don't just retry with a guess.

---

## Included Scripts

### safe_backup.py — Snapshot & Revert
Create timestamped snapshots before editing, list all versions, revert instantly.

```bash
python scripts/safe_backup.py snapshot file.py "before refactor"
python scripts/safe_backup.py list file.py
python scripts/safe_backup.py revert file.py          # latest
python scripts/safe_backup.py revert file.py 2         # specific snapshot
python scripts/safe_backup.py diff file.py             # diff current vs backup
```

ALWAYS snapshot before a batch edit. The revert creates its own safety snapshot first, so you can never lose work.

### batch_replace.py — Validated Batch Edits
Apply multiple replacements in one pass with validation, dry-run, and unicode diagnostics.

```bash
# Preview what would change (ALWAYS do this first):
python scripts/batch_replace.py target.js replacements.json --dry-run

# Apply with automatic backup:
python scripts/batch_replace.py target.js replacements.json --backup
```

The replacements.json format:
```json
[
    {"old": "original text here", "new": "replacement text here"},
    {"old": "another string", "new": "its replacement"}
]
```

The script validates ALL replacements before applying any:
- Reports strings not found (with unicode mismatch diagnostics)
- Warns about ambiguous matches (string found more than once)
- Applies everything in one pass (no cascade failures)

### validate_file.py — Post-Edit Integrity Check
Validates files after editing to catch breakage early.

```bash
python scripts/validate_file.py edited_file.py
python scripts/validate_file.py *.js *.json
python scripts/validate_file.py --all src/    # recursive
```

Checks per file type:
- Python: AST syntax parse
- JavaScript/TypeScript: Node --check
- JSON: structure validation
- YAML: safe_load parse
- XML/HTML/SVG: tag balance
- All files: encoding, line endings, null bytes

## Recommended Workflow for Complex Edits

```bash
# 1. Snapshot the original
python scripts/safe_backup.py snapshot target.js "before typography fixes"

# 2. Prepare replacements file
# (write your replacements.json)

# 3. Dry-run to validate
python scripts/batch_replace.py target.js replacements.json --dry-run

# 4. Fix any NOT FOUND or AMBIGUOUS issues in replacements.json

# 5. Apply
python scripts/batch_replace.py target.js replacements.json --backup

# 6. Validate the result
python scripts/validate_file.py target.js

# 7. If something went wrong:
python scripts/safe_backup.py revert target.js
```

---

*This skill emerged from patterns observed across hundreds of editing sessions, in collaboration with [@PGTBoos](https://github.com/PGTBoos). The failure modes are predictable and preventable — but only if you have a strategy before you start editing.*
