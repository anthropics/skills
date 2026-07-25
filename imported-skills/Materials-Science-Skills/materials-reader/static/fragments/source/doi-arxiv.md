# Source: DOI or arXiv identifier

The user gave a bare DOI or arXiv id/link that must be resolved before reading.

- Resolve the identifier to the actual article first:
  - DOI → the publisher landing page (ScienceDirect, Springer, Taylor & Francis, MDPI), then the open-access PDF or HTML if available.
  - arXiv → the abstract page, then the PDF.
- After resolving, this becomes a `pdf-text`, `scanned-pdf`, or `html` job — load that fragment and follow it for extraction. This fragment only covers retrieval.
- Capture bibliographic metadata (title, authors, journal, year, DOI) for the `paper.md` identity section.
- Prefer the open-access version when the version of record is paywalled. Note which version was read in `translation_notes.md`.
- For CBM/CCC/JBE papers on ScienceDirect, the HTML version often has cleaner table markup than the PDF. Consider loading `html` fragment instead.
- If the identifier cannot be resolved or only the abstract is reachable, build a draft reader from what is available and clearly mark the rest as not retrieved. Do not fabricate body text.
