# Cover Letter Strategy

## Inputs

- Manuscript title and abstract (from writing state or manifest).
- Journal cover_letter_required_points (from journal-templates yaml).
- Declarations (from manifest).

## Generation

The LLM fills the 7-paragraph structure from
`materials-writing/static/fragments/section/cover-letter.md`:

1. Editor address and date
2. Salutation
3. Submission statement (title, article type, journal)
4. Core contribution (one paragraph)
5. Fit to journal (one sentence)
6. Suggested reviewers / conflicts (only if supplied)
7. Closing

## Boundary

Do not invent declarations, suggested reviewers, funding, or conflicts.
If a field is empty in the manifest, leave a `[LIVE-VERIFICATION: ...]`
placeholder. This boundary mirrors
`materials-polishing/references/cover-letter.md`.
