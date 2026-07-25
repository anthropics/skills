# HTML Deck Contract

A generated deck must be a retained browser-native HTML deck directory and
should include:

- `index.html` browser presentation shell,
- `slides/` with one independent HTML file per slide,
- `shared/tokens.css` with deck-wide visual tokens,
- `screenshots/` from strict Playwright verification,
- `qa_report.md` and `qa_report.json`,
- `asset_manifest.json`,
- `speaker_notes.json` when notes are available.

The narrative should include:

- title slide,
- engineering problem,
- material design or paper identity,
- experiment/evidence chain,
- key results,
- mechanism or interpretation,
- limitations,
- next steps.

When requested, crop figures before deck generation, preserving axes, legends,
labels, and scale bars. If information is missing, keep the placeholder visible
rather than inventing content.
