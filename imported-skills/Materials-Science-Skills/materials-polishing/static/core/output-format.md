# Output format

Default output:

1. The polished text as plain prose, not in a code block.
2. `Revision notes:` with `3-5` short bullets on the major structural and stylistic changes.
3. If the rewrite changed section logic, say so explicitly.

If the user asks for side-by-side revision, provide:

- `Original`
- `Polished`
- `Why changed`

If any paragraph's structural problem could not be fixed without inventing content, say so under `Revision notes:` instead of papering over it.

## Materials-science-specific output conventions

- Preserve all quantitative data exactly as written: values, units, significant figures, and error bars.
- Do not alter test standard references (ASTM, ISO, GB) or specimen dimensions.
- When correcting terminology, list all changes in `Revision notes:` so the author can verify domain-specific usage.
- If a sentence contains a mechanism claim (e.g., "GO promotes C-S-H nucleation"), flag it in `Revision notes:` as a claim that requires evidence verification.
- Preserve LaTeX commands and citation keys unchanged.
