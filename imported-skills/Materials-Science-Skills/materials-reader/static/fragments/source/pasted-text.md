# Source: pasted text or notes

The user pasted prose, abstract, or notes directly, with no retrievable original layout or page images.

- Treat the pasted text as the source of truth. Build the source map and bilingual pairs from it.
- Page numbers may be unknown. Use sequential block IDs (`S001`, `S002`, ...) and, where the paste shows section headings, use section-level anchors. Note in `translation_notes.md` that page anchors are unavailable.
- There are usually no figure/table images. Do not invent crops. If the text references figures/tables, keep the references and captions as text blocks and note that visual assets were not provided.
- If the paste is clearly partial (e.g., abstract and introduction only), build the reader for what was given and label it draft mode; do not backfill missing sections from memory.
- Preserve any citation markers, equations, and symbols exactly as pasted.
- Keep the bilingual reader format; do not collapse pasted prose into a summary just because layout metadata is missing.
- For WER-EA papers, still extract material system, dosage, and test conditions into structured fields even from a partial paste.
