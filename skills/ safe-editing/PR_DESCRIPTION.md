# Pull Request: New Skill — safe-editing

## Title (for the PR title field):
Add safe-editing skill: safe strategies for multi-edit and multi-file code modifications

## Description (copy-paste this into the PR description):

### What this skill does

Prevents common failure modes when Claude makes multiple edits to files:

- **Non-unique match failures**: `str_replace` refusing because the search string appears more than once
- **Cascade failures**: early edits breaking the context for later edits in the same file
- **Unicode encoding mismatches**: literal characters vs escape sequences (`é` vs `\u00E9`) causing silent failures
- **No rollback**: half-edited files when something fails mid-sequence
- **Context drift**: Claude's mental model of the file diverging from reality after several edits

These problems are invisible from the outside — Claude eventually recovers, retries, or rewrites. But the waste adds up: extra tool calls, inconsistent files, frustrated users waiting for edits that keep failing.

### How it works

The skill provides both strategic guidance (when to use `str_replace` vs batch scripts vs full rewrites) and three concrete scripts:

**safe_backup.py** — Snapshot and revert system
```bash
python scripts/safe_backup.py snapshot file.py "before refactor"
python scripts/safe_backup.py revert file.py
python scripts/safe_backup.py diff file.py
```

**batch_replace.py** — Validated batch edits in a single pass
```bash
python scripts/batch_replace.py target.js replacements.json --dry-run
python scripts/batch_replace.py target.js replacements.json --backup
```
Validates ALL replacements before applying any. Detects unicode mismatches, ambiguous matches, and missing strings — with diagnostics explaining why.

**validate_file.py** — Post-edit integrity check
```bash
python scripts/validate_file.py edited_file.py
python scripts/validate_file.py --all src/
```
Syntax validation per file type: Python AST, Node --check, JSON, YAML, XML tag balance, encoding and line ending consistency.

### The recommended workflow
1. Snapshot the original
2. Write replacements as JSON
3. Dry-run to validate
4. Fix any issues
5. Apply with backup
6. Validate the result
7. Revert if needed

### Origin

This skill emerged from collaboration between [@PGTBoos](https://github.com/PGTBoos) and Claude. As a developer who works extensively with Claude on larger codebases, @PGTBoos kept diagnosing the same recurring editing failures — unicode mismatches, cascade breaks, missing rollback — much like a doctor identifying a pattern of symptoms that the patient doesn't notice individually. The insight was that these aren't random glitches but predictable, preventable failure modes that deserve a systematic treatment plan rather than ad-hoc recovery each time.

### Checklist
- [x] SKILL.md with valid YAML frontmatter (name + description)
- [x] Three self-contained Python scripts with no external dependencies
- [x] Dry-run mode for safe preview
- [x] Automatic backup and revert capability
- [x] Unicode mismatch diagnostics
- [x] Post-edit validation for common file types
- [x] Tested during real multi-edit sessions (200+ replacements in document generation)
