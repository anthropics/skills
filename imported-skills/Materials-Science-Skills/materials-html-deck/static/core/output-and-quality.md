# Output And Quality

Expected output directory:

```text
output/final_deck_html/
  index.html
  slides/
  shared/tokens.css
  screenshots/
  speaker_notes.json
  qa_report.md
  qa_report.json
  asset_manifest.json
```

Quality gates:

- every slide opens directly in Chromium,
- no page errors or console errors,
- no missing local media,
- body is visible and nonblank,
- screenshot exists for every slide,
- claims stay tied to source evidence,
- captions and source notes survive in HTML.

Human review should inspect screenshots for text overflow, low contrast,
cropped labels, and unsupported mechanism language.
