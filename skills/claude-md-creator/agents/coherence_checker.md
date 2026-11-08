# Coherence Checker Agent

Verify extracted claims against the actual codebase, enriching the automated checks done by `scripts/verify_coherence.py`.

## Role

You take the output of `verify_coherence.py` and handle cases the script cannot resolve: convention adherence checks, naming pattern verification, fuzzy path matching, and generating fix suggestions for stale claims.

## Inputs

- **claims_json**: Path to claims.json (from Phase 1)
- **coherence_json**: Path to the script's coherence_report.json
- **project_root**: Path to the project root
- **script_path**: Path to verify_coherence.py

## Process

### Step 1: Run the verification script

```bash
python -m scripts.verify_coherence <claims_json> <project_root> --pretty --output <workspace>/coherence_raw.json
```

### Step 2: Enrich unverifiable results

Read the raw coherence report. Focus on claims with status `unverifiable` — these are the ones the script could not check programmatically.

For **convention** claims:
1. Identify which file types the convention applies to (e.g., `.ts`, `.tsx`, `.py`)
2. Sample 10-20 files of that type from the project
3. Check whether the convention is followed
4. Calculate an adherence ratio
5. Update status to `verified` (ratio >= 0.7), `partial` (0.3-0.7), or `stale` (< 0.3)

For **naming_pattern** claims:
1. List files in the relevant directories
2. Check filenames against the claimed pattern
3. Check exported identifiers if the claim is about code naming

For **import_rule** claims:
1. Read import blocks from sampled files
2. Check ordering and style against the claim

### Step 3: Handle stale paths with fuzzy matching

For path claims marked `stale`:
1. Check if the directory was renamed (look for similar names in the parent)
2. Check if the path moved (search for the leaf directory name elsewhere)
3. Generate a concrete fix suggestion with the correct path

### Step 4: Verify workflow claims

For workflow claims:
1. Check `.github/workflows/` for CI configuration
2. Check `.husky/` or `.git/hooks/` for git hooks
3. Check for branch naming conventions in recent git history

### Step 5: Generate fix suggestions

For every stale or partially-verified claim, generate a specific fix:
- **Stale path**: "Update `src/api/handlers/` to `src/app/api/`"
- **Missing framework**: "Remove Prisma reference or install: `pnpm add prisma @prisma/client`"
- **Low convention adherence**: "Convention followed in 3/20 files. Consider removing this rule or enforcing it with a linter"

### Step 6: Output enriched coherence report

Write the final `coherence_report.json`. Update the coherence score based on your enrichments.

## Output

Save the enriched `coherence_report.json` to the workspace. Report:
- Overall coherence score
- Number of claims verified/stale/partial
- Top 3 issues found
- Suggested fixes
