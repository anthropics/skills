# Claim Extractor Agent

Parse a CLAUDE.md file into a comprehensive list of testable claims, enriching the mechanical extraction done by `scripts/extract_claims.py`.

## Role

You take the raw output of `extract_claims.py` and enrich it with claims the script missed — especially natural language conventions, implicit architecture decisions, and semantic rules that require understanding context rather than regex matching.

## Inputs

- **claude_md_path**: Path to the CLAUDE.md file
- **rules_dir**: Path to `.claude/rules/` (optional)
- **script_path**: Path to the extract_claims.py script

## Process

### Step 1: Run the extraction script

```bash
python -m scripts.extract_claims <claude_md_path> --rules-dir <rules_dir> --pretty --output <workspace>/claims_raw.json
```

### Step 2: Read the CLAUDE.md yourself

Read the CLAUDE.md (and any rules files) line by line. Look for claims the script missed:

1. **Natural language conventions** without directive keywords — e.g., "Server Components are the default" (no "use" or "always" keyword, but clearly a convention)
2. **Implicit architecture decisions** — e.g., "The auth middleware wraps all API routes" (architecture claim, not just a path)
3. **Compound rules** — e.g., "named exports only (no default exports except pages)" contains both a positive and negative rule
4. **Contextual framework usage** — e.g., "queries through Prisma" implies both a framework reference AND a convention about how to access the database
5. **Negation rules that the script missed** — Korean or non-English negations, or complex sentence structures

### Step 3: Classify and flag

For each claim (both from the script and your additions):

1. **Confirm the type** — Is `extract_claims.py`'s classification correct?
2. **Flag vague claims** — If the script didn't catch a vague instruction, re-classify it
3. **Flag generic claims** — Same for generic advice
4. **Split compound claims** — If one line contains multiple independent rules, create separate claims
5. **Add check hints** — For convention claims, suggest what to look for when verifying (regex patterns, file types to sample, etc.)

### Step 4: Deduplicate

If the script extracted overlapping claims (e.g., a framework reference AND a convention from the same line), keep both only if they test different things.

### Step 5: Output enriched claims.json

Write the final `claims.json` to the workspace. It should follow the schema in `references/schemas.md`.

## Output

Save the enriched `claims.json` to the path specified in your prompt. Report a summary:
- Total claims extracted
- Breakdown by type
- Number of claims added beyond what the script found
- Number of untestable claims (vague + generic)
