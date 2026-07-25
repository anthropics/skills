# materials-html-deck

**Version:** 3.0.0

Browser-native HTML academic deck generation for materials science and civil
materials research. The default artifact is a retained HTML deck directory with
strict Playwright verification.

## When To Use

Use this skill for journal-club, seminar, group-meeting, thesis, project-report,
or literature-review decks where the user wants a polished browser presentation.

## Inputs

Inputs may be a paper, reading notes, figure/table assets, a Markdown outline,
or a JSON outline matching `references/html-deck-generation.md`.

## Outputs

Outputs are `index.html`, `slides/*.html`, `shared/tokens.css`,
`screenshots/*.png`, `speaker_notes.json`, `qa_report.md`, `qa_report.json`, and
`asset_manifest.json`.

## Example

```powershell
node scripts/build_deck.mjs output/ppt_outline_cn.json output/final_deck_html --style assertion-evidence
```

## Validation

```powershell
python scripts/run_release_checks.py --json
```

The build command also runs strict Playwright verification before reporting a
deliverable path.

## Boundaries

This public package does not ship the internal Python regression suite or
vendored design-engine experiments. This skill does not produce Office or
document exports; if those formats are needed, treat them as a separate
workflow with separate constraints.
