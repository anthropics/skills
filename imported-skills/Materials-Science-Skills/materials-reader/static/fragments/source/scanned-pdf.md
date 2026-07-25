# Source: scanned PDF (OCR required)

The PDF is image-only or has an unreliable text layer. Use OCR before building the reader.

- OCR every page; do not assume a usable text layer exists.
- Record a confidence level for each block in the source map, and mark low-confidence blocks in `translation_notes.md` rather than guessing.
- Preserve original wording where OCR is confident; flag, do not silently "correct", garbled text.
- Be careful with numerals, units, symbols, and chemical formulas — OCR errors here change meaning. Cross-check against context and mark uncertainty.
- Chinese journal scans may have mixed Chinese/English text. OCR both layers; do not discard the Chinese portion.
- Figures and tables are page regions: crop per `references/pdf-visual-asset-extraction.md`. For low-quality scans, a tight correct crop still beats a wide noisy one.
- SEM/AFM images in scans lose significant detail. Note in `translation_notes.md` when microstructure interpretation is limited by scan quality.
- If pages are skewed, rotated, or partly cut off, note the affected pages and translate only what is legible.
