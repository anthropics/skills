# Link Validation Report - Anthropic Skills Repository

**Date:** 2026-02-12  
**Repository:** https://github.com/anthropics/skills  
**Validator:** comprehensive-link-validator.sh

---

## Executive Summary

✅ **Validation Status:** PASSED (after fixes)  
📄 **Files Scanned:** 44 markdown files  
⚠️  **Issues Found:** 8 case mismatches (FIXED)  
ℹ️  **Warnings:** 20 documentation examples (expected)

---

## Issues Discovered

### 1. Case Sensitivity Issues in `skills/pdf/SKILL.md`

**Problem:** The skill referenced uppercase filenames (`FORMS.md`, `REFERENCE.md`) but actual files use lowercase (`forms.md`, `reference.md`).

**Impact:** On case-sensitive filesystems (Linux, macOS with APFS case-sensitive), these references would fail to resolve correctly, potentially breaking Claude's skill loading mechanism.

**Occurrences:** 8 instances total
- `REFERENCE.md` → should be `reference.md` (4 occurrences)
- `FORMS.md` → should be `forms.md` (4 occurrences)

**Locations:**
```
Line 11:  "see REFERENCE.md" → "see reference.md"
Line 11:  "read FORMS.md" → "read forms.md"
Line 307: "see FORMS.md" (table) → "see forms.md"
Line 307: "See FORMS.md" (table) → "See forms.md"
Line 311: "see REFERENCE.md" → "see reference.md"
Line 312: "see REFERENCE.md" → "see reference.md"
Line 313: "in FORMS.md" → "in forms.md"
Line 314: "see REFERENCE.md" → "see reference.md"
```

**Root Cause Analysis:**

The repository follows a consistent naming convention:
- **UPPERCASE:** Only for standard files (`SKILL.md`, `LICENSE.txt`)
- **lowercase/kebab-case:** All reference/example files

This is confirmed by the README.md (line 85): "name - A unique identifier for your skill (lowercase, hyphens for spaces)"

The `skills/skill-creator/SKILL.md` documentation contains examples using UPPERCASE references (e.g., `FORMS.md`, `REFERENCE.md`), which appears to have been incorrectly copied into the pdf skill without adjusting for the actual lowercase filenames.

**Fix Applied:**
All 8 occurrences in `skills/pdf/SKILL.md` were updated to use lowercase filenames, matching the actual file naming convention.

---

## Validation Against Repository Standards

### Naming Convention Analysis

Analyzed all 44 markdown files in the repository:

**Pattern Observed:**
- `SKILL.md` files: 16 instances (all UPPERCASE) ✓
- Other reference files: 24 instances (all lowercase) ✓
- Examples:
  - `forms.md`, `reference.md`, `editing.md` (lowercase)
  - `arctic-frost.md`, `company-newsletter.md` (kebab-case)
  - `mcp_best_practices.md` (snake_case)

**Conclusion:** The pdf skill's UPPERCASE references were inconsistent with repository-wide conventions.

---

## Warnings (Non-Issues)

20 warnings were flagged in `skills/skill-creator/SKILL.md`:
- `FORMS.md`, `REFERENCE.md`, `EXAMPLES.md`, etc.

**Assessment:** These are **documentation examples** showing how to structure skills, not actual file references. They appear in code blocks and example snippets teaching developers how to create their own skills. No action required.

---

## Technical Details

### Validation Methodology

The validation script (`comprehensive-link-validator.sh`) performs three checks:

1. **Markdown link validation** - Validates `[text](path)` syntax links
2. **Plain text reference validation** - Detects file mentions like "see FILE.md"
3. **Case sensitivity check** - Compares references against actual filesystem (case-sensitive)

**Exclusions:**
- HTTP/HTTPS URLs (external links)
- `mailto:` links
- Pure anchor links (`#section`)
- `THIRD_PARTY_NOTICES.md` (contains email addresses)

### Files Validated

All 44 markdown files across:
- 16 skills directories
- Reference documentation
- Examples and templates
- Root-level documentation

---

## Recommendations

### 1. For Repository Maintainers

**✅ DONE:** Fix case mismatches in `skills/pdf/SKILL.md`

**Future Prevention:**
- Add CI/CD check using the validation script
- Document naming conventions explicitly in contribution guidelines
- Consider adding pre-commit hook for link validation

### 2. For Skill Creators

**Naming Convention Best Practices:**
- Use **lowercase** for all reference/example files
- Use **kebab-case** for multi-word filenames
- Reserve **UPPERCASE** only for `SKILL.md` and `LICENSE.txt`
- Verify references match actual filenames (case-sensitive)

### 3. Documentation Improvements

The `skills/skill-creator/SKILL.md` examples use UPPERCASE references, which conflicts with repository practice. Consider:
- Update examples to use lowercase (aligns with reality)
- Add explicit note about lowercase convention
- Show both correct and incorrect examples

---

## Verification

### Before Fix
```bash
$ ./comprehensive-link-validator.sh
❌ Total issues: 8
⚠️  Case mismatches: 8
```

### After Fix
```bash
$ ./comprehensive-link-validator.sh
✅ No critical issues found!
📄 Scanned files: 44
❌ Total issues: 0
```

---

## Conclusion

All critical link validation issues have been resolved. The repository now maintains consistent naming conventions across all markdown files. The validation script can be integrated into CI/CD pipelines to prevent future regressions.

**Status:** ✅ READY FOR MERGE

---

## Appendix: Validation Script

The validation script is available at:
`./comprehensive-link-validator.sh`

**Usage:**
```bash
chmod +x comprehensive-link-validator.sh
./comprehensive-link-validator.sh
```

**Output:**
- Terminal: Color-coded results
- File: `link-validation-report.txt` (plain text log)

---

**Generated by:** comprehensive-link-validator.sh  
**Validator Author:** m4p1x  
**Date:** 2026-02-12
