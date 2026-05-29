<!-- READ-ONLY: Update data sources, not this template. -->
# Ninth Circuit Motion Template (Block Library)

> **Purpose:** Instead of one huge motion shell, we now have small blocks that can be snapped together in any order (cover → intro → facts → argument, etc.). Feed the sequence + data through JSON and let the generator stitch the blocks into a DOCX/PDF.

---

## 0. Metadata & Block Sequence
```json
{
  "court_name": "United States Court of Appeals for the Ninth Circuit",
  "case_number": "No. 24-1234",
  "case_title": "MARK A. GALELLI, Plaintiff-Appellant v. COUNTY OF CLACKAMAS, et al.",
  "motion_title": "APPELLANT'S EMERGENCY MOTION FOR STAY PENDING APPEAL",
  "moving_party": "Mark A. Galelli",
  "emergency_basis": "the district court set execution for December 8, 2025",
  "relief_requested": [
    "Stay enforcement of the March 6, 2025 general judgment",
    "Order expedited briefing on this motion"
  ],
  "legal_standard": {
    "heading": "A stay pending appeal turns on four factors:",
    "points": [
      "Likelihood of success on the merits",
      "Likelihood of irreparable harm absent relief",
      "Balance of equities",
      "Public interest"
    ]
  },
  "supporting_citations": ["FRAP 8(a)", "FRAP 27", "Ninth Cir. R. 27-1"],
  "motion_facts": [
    { "statement": "On March 6, 2025 the court entered judgment without notice.", "record_cite": "ER-12" }
  ],
  "arguments": [
    { "heading": "I. The Appeal Raises Serious Questions", "text": "{{argument_text}}" }
  ],
  "attachments": ["Exhibit 1 – Order (ECF 67)"],
  "service_list": ["Counsel Name, Firm, Email"],
  "signature_block": "Mark A. Galelli, Pro Se",
  "word_count": 0,
  "service_date": "December 7, 2025",
  "block_sequence": [
    "10_caption",
    "20_introduction",
    "30_factual_background",
    "40_legal_standard",
    "50_argument_section",
    "60_relief",
    "70_attachments",
    "80_certificate_compliance",
    "90_certificate_service"
  ]
}
```

- `block_sequence` drives the order. Swap entries (e.g., send introduction → factual background → jurisdiction → argument) without editing the blocks.
- Block files live in `templates/motion_blocks`. Add new files and reference them here when you need extra structure (e.g., procedural history, declarations).

---

## 1. Block Reference

| Block ID | File | Description | Inputs |
| --- | --- | --- | --- |
| `00_cover` | `motion_blocks/00_cover.md` | Optional cover sheet | `court_name`, `case_number`, `motion_title`, `filing_date`, `relief_requested[]` |
| `10_caption` | `motion_blocks/10_caption.md` | Caption + title | `court_name`, `case_title`, `case_number`, `motion_title` |
| `20_introduction` | `motion_blocks/20_introduction.md` | Relief summary paragraph(s) | `moving_party`, `relief_requested[]`, `emergency_basis` |
| `30_factual_background` | `motion_blocks/30_factual_background.md` | Fact paragraphs | `motion_facts[]` (`statement`, `record_cite`) |
| `32_jurisdiction` | `motion_blocks/32_jurisdiction.md` | Jurisdiction or authority statements | `jurisdiction_blocks[]` |
| `40_legal_standard` | `motion_blocks/40_legal_standard.md` | Tests / factors | `legal_standard.*`, `supporting_citations[]` |
| `50_argument_section` | `motion_blocks/50_argument_section.md` | Each argument heading + body (loop) | `arguments[]` (`heading`, `text`, optional `footnotes[]`) |
| `60_relief` | `motion_blocks/60_relief.md` | Conclusion + signature | `moving_party`, `relief_requested[]`, `signature_block` |
| `70_attachments` | `motion_blocks/70_attachments.md` | Exhibit index | `attachments[]` |
| `80_certificate_compliance` | `motion_blocks/80_certificate_compliance.md` | Word-count certification | `word_count` |
| `90_certificate_service` | `motion_blocks/90_certificate_service.md` | Service list | `service_date`, `service_list[]` |

Add more (e.g., `35_procedural_history`, `55_standard_of_review`) by dropping a new file into `motion_blocks/` and referencing it in the sequence.

---

## 2. How to Render

1. **Load data** from `case_info.json`, `argument_content.json`, `evidence_pool.json`, `timeline.json`, and motion-specific metadata.
2. **Map facts** – tag fact entries with `"used_in_sections": ["motion_facts", "motion_I"]` so the generator knows which ones to drop into `motion_facts[]`.
3. **Build block payloads** – for each block ID in `block_sequence`, gather the inputs listed above (e.g., `legal_standard` object, `arguments[]`).
4. **Render markdown** – concatenate the block files in sequence, substitute data using your templating engine (Mustache/Jinja/Handlebars), then convert to DOCX with the same toolchain as `BRIEF_SHELL.md`.
5. **Post-process** – update TOC/page numbers, insert word count, and log the run in `OUTBOX/chronological/motion-log.json`.
6. **Distribute** – save to `legal_brief_system/output/` and copy to `OUTBOX/motions/` and `OUTBOX/chronological/` (timestamped, read-only).

---

## 3. Guardrails & Notes

- **No paraphrasing** – every block expects verbatim text from the JSON sources or the pleading banks. If edits are needed, change the source JSON before regenerating.
- **One relief type per motion** – keep procedural vs substantive requests in separate runs to satisfy FRAP 27 and Local Rule 27.
- **Attachments** – FRAP 27(a)(2)(B)(iii) requires attaching the order being challenged. Ensure `attachments[]` includes it, and fail generation if the file is missing.
- **Word limits** – set `word_count` from the rendered document (5200-word cap for motions/responses; 2600 for replies).
- **Single-agent flow** – all automation runs through this template + data. No hidden prompts or helper agents may rewrite the text.

For a deeper walkthrough (data sources, logging, future CLI hooks), see `skills/ninth-circuit-brief-body/references/motion-template-guide.md`.
