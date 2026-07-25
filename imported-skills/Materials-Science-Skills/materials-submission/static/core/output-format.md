# Submission Package Output Format

The submission package is a directory, not a single file.

## Directory shape

```text
submission-package/
  MANIFEST.md
  submission-package.yaml
  cover-letter.md
  highlights.md
  keywords.md              # when required by the article route
  declarations.md          # when required by the article route
  submission-checklist.md
  manuscript/SOURCE.md
  figures/SOURCE.md
  data/SOURCE.md
  reviewer-risk-regression.md
```

## MANIFEST.md

Lists every artifact in the package with its source path, status, and
live-verification flag. One row per artifact.

## submission-package.yaml

Machine-readable handoff conforming to
`_shared/contracts/submission-package.yaml`. It includes the resolved
submission manifest path, package directory, journal/article route, generated
artifact paths and statuses, optional writing/figure/FAIR input statuses, gate
statuses, and live-verification placeholders.

## Placeholder convention

- `[LLM: ...]` marks paragraphs the LLM must fill from prepared inputs.
- `[LIVE-VERIFICATION: ...]` marks fields the user must re-check against
  the current Guide for Authors before submission.

## Dry-run output

`--dry-run` prints the intended `MANIFEST.md` and the list of files that
would be written, without creating the directory.
