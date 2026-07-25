# Submission Package Contract

`materials-submission` produces a submission package directory. It does not
replace manuscript writing, figure production, FAIR packaging, or final
publisher-guide verification.

## Inputs

- `submission-manifest.yaml`: target journal, accepted article type, title,
  corresponding author, declaration statuses, and optional source paths.
- The matching `_shared/journal-templates/<journal>.yaml` and `.md` files.
- Optional manuscript, figure, FAIR-data, and reviewer-routing artifacts.

## Outputs

- `MANIFEST.md`, `cover-letter.md`, and `submission-checklist.md`.
- `keywords.md` and `declarations.md` only when the selected article route
  requires the matching template fields.
- `highlights.md` only when `highlights_required` is true.
- Source stubs for manuscript, figures, and data.

## Refusal conditions

The builder emits dry-run output instead of a final package when:

- `live_verification_acknowledged` is false.
- The journal has no supported template.
- The requested article type is unavailable to the selected journal.
- Data availability is pending without a FAIR package path.
- Title or corresponding author is missing.

## Evidence boundary

Declarations remain user values or live-verification placeholders. The
checklist lists journal-specific submission and revision artifacts from the
selected YAML template.
