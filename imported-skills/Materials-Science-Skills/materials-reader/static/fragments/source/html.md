# Source: publisher or preprint HTML

The source is an HTML page (ScienceDirect, Springer, MDPI, Taylor & Francis, or preprint server).

- Extract the article body; strip site navigation, cookie banners, related-article rails, and advertisements.
- Keep the section structure and paragraph order from the article markup.
- Publisher HTML tables are often cleaner than PDF-extracted tables. Prefer HTML table markup over screenshotting when the structure is intact.
- Figures are usually separate `<img>` or `<figure>` elements — capture each figure image and its caption, and place per `references/pdf-visual-asset-extraction.md`.
- Preserve inline math, superscript citation markers, and links to the reference list.
- ScienceDirect HTML often includes supplementary material links — note their availability in `translation_notes.md` even if not fully extracted.
- Respect the copyright caution: for paywalled pages, keep chat output short and point to the local artifact. Reproduce full bilingual text only for clearly lawful open-access content.
- If the page is JavaScript-rendered and content is missing, note what could not be retrieved instead of inventing it.
