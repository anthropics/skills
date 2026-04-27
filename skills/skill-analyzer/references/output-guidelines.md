# Output Guidelines

## File path

Write to `skill-analysis-{skill-name}.md` in the current working directory, or the path the user specifies.

## Rules

- Scores: integer 1–5 only, never a range or decimal
- Tokens: rounded to nearest 10 (e.g. `~860`)
- "Skill adds" line: one sentence, name the specific guidance item(s) — no generic statements
- VERDICT: exactly `USE IT`, `SKIP IT`, or `PARTIAL [list phases]`
- Do not output the component list from Step 0 — use it internally only
- Maximum 2 scenarios unless the user asks for more

## Quality score

| Score | Meaning |
|-------|---------|
| 5/5 | Specific params, code, or diagnostics Claude can't reliably reproduce |
| 4/5 | Skill meaningfully guides this phase |
| 3/5 | Some guidance, Claude handles it adequately alone |
| 2/5 | Adjacent territory, won't change the outcome |
| 1/5 | Mismatch — wastes context |

Phase verdict: 4–5 → KEEP · 3 → OPTIONAL · 1–2 → DROP

## Verification

After writing, read the file back and confirm: no `{{PLACEHOLDER}}` remains · every VERDICT uses exact wording · Overall table covers all phases.
