# Source: Scanned PDF (OCR Required)

Use when the PDF is image-only or has very low extractable text. OCR is
**out of scope for this skill** — call an external OCR tool (Tesseract,
PaddleOCR, Adobe) and feed the result back as `pasted-text.md`.

## Risk flags

- Every OCR'd block whose confidence is below acceptable threshold gets
  `support_status = needs-confirmation`.
- Equations from OCR are particularly fragile — mark every symbol as
  `[TO CONFIRM: ...]` and exclude from formal claims until verified.
- Do not guess. Patent prosecution cannot un-ring the bell of a wrongly
  claimed symbol.

## Handoff

After external OCR, route the result through `pasted-text.md` workflow.
