# Fulltext Figure-Anchored Reading

> **Domain context**: The `domain` axis has loaded domain-specific reading guidance for [detected domain]. The reader package structure below is universal; the domain guide lists domain-specific evidence to prioritize.

Use this reference when turning a PDF, publisher HTML, pasted full text, or extracted text into a source-grounded `paper.md` for review work across all material domains.

## Required products

Produce these linked artifacts when the user asks for full reading, intensive reading, paper.md, paper notes, figure/table anchoring, or review extraction:

- `paper.md`: the human-readable reading note.
- `source_map.json`: machine-readable anchors linking claims, excerpts, figures, tables, pages, sections, and borrowable writing.
- `translation_notes.md`: term normalization, Chinese understanding, translation-risk notes, and non-copyable writing moves.
- `figure_table_cards.md`: structured cards for each important visual or data table.
- `mechanism_evidence_table.md`: reviewer-safe rows that separate measured evidence, inferred mechanism, and missing evidence.

For domain-specific tables (e.g., dosage optimization for civil, sintering parameters for ceramics, processing parameters for metals), create supplementary tables as needed.
- `obsidian_note.md`: three-layer Obsidian note for the user's WER-EA knowledge graph.
- `visual_asset_spec.json`: source-page and crop-box specification for PDF visual assets.
- `assets/`: cropped figures, rendered pages, extracted tables, `asset_manifest.md`, `visual_asset_report.json`, `contact_sheet.png`, or explicit failure records.

For WER-EA 30-paper reading packages, also load `wer-ea-intensive-reading-package.md`.

## `paper.md` contract

Every `paper.md` must contain:

1. Paper identity: title, year, journal, DOI if known, source path or URL, and extraction status.
2. Reading route: source type, material domain, WER-EA relevance, and intended use in the user's mini-review.
3. Original excerpt blocks: exact source snippets with page/section/figure/table anchors. Keep excerpts short and tied to one claim.
4. Chinese understanding: a Chinese explanation of what the excerpt actually supports, including uncertainty and missing evidence.
5. Figure card and table card index: one line per figure/table, with evidence role and claim boundary.
6. Source-grounded mechanism chain: claim -> original excerpt -> measured evidence -> mechanism interpretation -> boundary.
7. Claim-evidence-boundary table: use the same wording discipline as reviewer-safe manuscript writing.
8. Borrowable writing: phrases, argument moves, methods language, and comparison logic the user can adapt without copying.
9. Mini-review handoff: citation role, table-system destination, figure-planning destination, and writing-outline destination.
10. Links to `translation_notes.md`, `mechanism_evidence_table.md`, `dosage_window_table.md`, `review_handoff.md`, `obsidian_note.md`, and `assets/`.

## WER-EA extraction focus

For WER-EA papers, always separate these evidence layers:

- Material system: asphalt/emulsion type, waterborne epoxy resin, curing agent, emulsifier, SBR or other modifiers, dosage, and preparation route.
- Literature screening role: whether the paper is central WER-EA evidence, adjacent modifier evidence, method evidence, durability evidence, or background only.
- Bonding performance: pull-off, shear, interlayer, tensile, moisture-conditioned, aged, or field/service-condition tests.
- Emulsion and construction properties: viscosity, storage stability, demulsification, mixing/workability, coating, and curing window.
- Mechanism evidence chain: FTIR, fluorescence microscopy, SEM/AFM, rheology, thermal analysis, phase morphology, and direct vs inferred mechanism.
- Durability boundary: wet conditioning, freeze-thaw, thermal aging, UV, traffic/service simulation, and whether field durability is actually supported.

## Figure card and table card rules

Each figure card or table card must answer:

- What is shown?
- Which claim can it support?
- Which claim is too strong?
- What source anchor proves this reading?
- What should be used in a literature-screening-table, mechanism-evidence-table, test-method-table, performance-comparison-table, durability-evidence-table, or journal-positioning-table?

Do not turn a figure caption into proof. A morphology image can suggest compatibility or phase structure, but mechanism claims need direct chemical, microstructural, rheological, or durability evidence.

## Source map rules

`source_map.json` must track:

- `source_id`
- `paper_id`
- `page`
- `section`
- `anchor_type`
- `anchor_label`
- `original_excerpt`
- `chinese_understanding`
- `claim_supported`
- `evidence_layer`
- `boundary`
- `borrowable_writing`
- `table_destination`
- `figure_destination`
- `downstream_files`

If page numbers are unknown, use `page: null` and keep section or figure/table labels explicit.

## Borrowable writing rules

Borrowable writing is not copied prose. It should be one of:

- a safe claim pattern,
- a methods-reporting phrase,
- a comparison sentence structure,
- a limitation sentence,
- a transition from performance to mechanism with bounded language.

Always include the boundary that prevents overclaiming.

## Asset rules

Use `assets/` for rendered pages, cropped figures, extracted tables, contact sheets, or source-inspection notes. If no image asset is available, create `assets/README.md` and state:

- source asset status,
- whether figures were visually inspected,
- which figures/tables need future rendering or cropping,
- which package files currently rely on text-only anchors.

When the source PDF is available, load `pdf-visual-asset-extraction.md`, create `visual_asset_spec.json`, and generate `assets/asset_manifest.md`, `assets/contact_sheet.png`, `assets/rendered_pages/`, and cropped `assets/figures/` or `assets/tables/`.
