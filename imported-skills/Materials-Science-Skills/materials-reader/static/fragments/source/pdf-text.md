# Source: selectable-text PDF

> **Domain context**: The `domain` axis has loaded domain-specific reading guidance. PDF extraction priorities may vary by domain — refer to the domain guide for domain-specific data to extract.

The PDF has an extractable text layer. Use `pymupdf` or `pdfplumber` for extraction.

- Extract the text layer directly; do not OCR text that is already selectable.
- Process the whole document, not just the first pages. Build the source map across every page.
- Watch for two-column layouts: recover reading order rather than raw stream order.
- Keep superscripts (m², cm⁻¹), subscripts (H₂O, Ca(OH)₂), and chemical formulas intact; rejoin words split across line breaks.
- Figures and tables are embedded images — crop them per `references/pdf-visual-asset-extraction.md`; do not paste page text where a table image belongs.
- Tables may span pages or have merged cells. Preserve the full table structure; note truncation in `translation_notes.md`.
- Extract test-condition rows (temperature, loading rate, specimen size, standard number) as structured data, not prose.
- If some pages are image-only, treat those with `scanned-pdf` rules and mark them with a confidence note.
