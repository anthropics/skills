# Submission Package Protocol

1. Read the manifest and selected journal template.
2. Read optional manuscript state, figure manifest, FAIR manifest, and
   reviewer-routing sources before required-field validation.
3. Let explicit submission-manifest values override writing-state metadata;
   use writing state only to fill missing title, abstract, authors,
   corresponding author, and keywords.
4. Validate the journal, article type, required live verification, title,
   corresponding author, and FAIR-data status. `ready` data availability needs
   a readable, parseable FAIR manifest.
5. Write `MANIFEST.md`, `submission-package.yaml`, cover letter, keywords,
   declarations, checklist, source stubs, and reviewer-risk record.
6. Write highlights only when the selected template requires them.
7. Render journal-specific artifacts in the checklist, grouped as
   initial-submission or revision requirements.
8. If a stale optional artifact has been manually changed, preserve the file and
   record its path, `ownership: user-preserved`, and hash in
   `submission-package.yaml`.
9. Preserve every live-verification placeholder until the user confirms the
   current publisher requirements.
