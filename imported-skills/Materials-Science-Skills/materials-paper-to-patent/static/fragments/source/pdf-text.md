# Source: Selectable PDF Text

Use when the user provides a PDF that already contains selectable text
(e.g., exported from a word processor, not a flat scan).

## Extraction

Run `scripts/extract_pdf_text.py` to produce a `.txt` file with per-page
markers (`===== PAGE N =====`). If the character count is below
`max(200, pages * 50)`, the PDF is probably scanned — fall back to
`scanned-pdf.md`.

## Provenance tagging

Each text block is given a stable ID `P001, P002, ...` in document order.
Page numbers and section headers are preserved. Equations become `E001...`,
figures become `F001...`. Do not paraphrase the source in the same file —
keep the original wording and tag it.

## Common pitfalls

- Header/footer lines repeating on every page — dedupe and tag once.
- Multi-column layouts — column reading order may be wrong; verify with
  the user before relying on extracted order.
- Inline images inside text — note as `Fxxx` references, not part of `Pxxx`.
