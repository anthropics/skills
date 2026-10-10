---
license: Provided under Anthropic's Terms of Service (not the Apache-2.0 LICENSE.txt used by most skills in this repo) — see NOTICE.md
source: https://github.com/anthropics/healthcare/tree/main/plugins/healthcare/skills/doc-extract
name: doc-extract
description: Extract plain text from a document file - PDF, DOCX, XLSX, PPTX, RTF, or plain text/markdown/HTML. Use when a binary document needs to be turned into text, for example a contract PDF or an EHR DocumentReference attachment. Other skills (fhir) invoke scripts/extract.ts directly; the contracts MCP server bundles its own copy (servers/documents/src/extract.mjs) so its bundle stays self-contained — port fixes to both.
---

# doc-extract

Shared document-to-text extraction. One script, no state: reads an input file, prints JSON to stdout, writes nothing to disk (PHI-safe — no caches, no temp files; callers own any caching).

## Setup (once)

```bash
cd <this skill dir> && bun install
```

This pulls [liteparse](https://www.npmjs.com/package/@llamaindex/liteparse) (the `lit` bin, used for PDF/DOCX/XLSX/PPTX, OCR included) and [rtf-to-text](https://www.npmjs.com/package/rtf-to-text) (RTF). Without it, PDFs still work via a `pdftotext -layout` fallback if poppler is installed; other binary formats require liteparse.

## Use

```bash
bun <this skill dir>/scripts/extract.ts <input-file> [--content-type <mime>]
```

Output on stdout:

```json
{ "text": "...", "method": "liteparse | pdftotext | rtf-to-text | passthrough", "pages": 12 }
```

- `text` is page-anchored for paged formats: `=== [page N] ===` markers between pages.
- `pages` is present when page markers exist.
- `method` is the extractor that actually produced the text.
- Format is taken from the file extension; pass `--content-type` (e.g. `application/pdf`) when the file has no useful extension, as with downloaded EHR attachments. Note liteparse refuses extension-less files, so those PDFs go through the `pdftotext` fallback.
- Errors print `{"error": "..."}` to stderr and exit 1.

## Table caveat

Tables with multiple value columns (option A vs option B, in-tier vs out-of-tier) can interleave columns line-by-line in the extracted text: fragments of adjacent cells alternate, and a cell's text can even land mid-sentence inside a neighboring column. Values usually survive, but which column a value belongs to can become ambiguous. When an answer comes from one column of a multi-column table and the document has no redundant restatement of the value elsewhere, verify it by reading the original page directly before treating it as ground truth. The extracted text's `=== [page N] ===` anchor tells you which page: pass it to the Read tool's `pages` parameter (e.g. pages: "37") to render just that page to vision instead of the whole document.

## For other skills

Import the functions instead of shelling out when you're already in bun TS:

```ts
import { extract, resolveLit } from "../doc-extract/scripts/extract";
const lit = resolveLit([myRoot]); // also checks myRoot/node_modules/.bin/lit
const text = extract(lit, "/path/to/file.pdf"); // string | null
```

The contracts skill consumes it this way (its ingest caching stays on the contracts side).
