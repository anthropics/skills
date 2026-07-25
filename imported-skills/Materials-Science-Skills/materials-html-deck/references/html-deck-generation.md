# HTML Deck Generation

The default command reads a JSON outline and writes a verified HTML deck
directory.

```powershell
node scripts/build_deck.mjs output/ppt_outline_cn.json output/final_deck_html --style assertion-evidence
node scripts/build_deck.mjs output/ppt_outline_cn.json --out-dir output/final_deck_html
node scripts/build_deck.mjs output/ppt_outline_cn.json --html-dir output/final_deck_html
```

The positional output, `--out-dir`, and `--html-dir` all mean the same thing:
the destination HTML directory. The command rejects Office or document output
paths and asks for an HTML directory instead.

The JSON outline supports the legacy fields:

- `title`
- `style_profile` or `academic_style`
- `slides[].title`
- `slides[].bullets`
- `slides[].takeaway`
- `slides[].images`
- `slides[].speaker_note` or `speaker_notes`

It also supports optional HTML-rich layout fields:

- `layout`
- `kicker`
- `subtitle`
- `metrics`
- `diagram`
- `evidence`
- `source_note`

Generated files:

- `index.html`
- `slides/*.html`
- `shared/tokens.css`
- `screenshots/*.png`
- `speaker_notes.json`
- `qa_report.md`
- `qa_report.json`
- `asset_manifest.json`
