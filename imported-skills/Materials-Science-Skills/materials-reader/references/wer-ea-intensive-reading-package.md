# WER-EA Intensive Reading Package

Use this protocol when a WER-EA, waterborne epoxy resin modified emulsified asphalt, waterproof-bonding, tack-coat, or adjacent pavement-bonding paper must become a reusable mini-review asset rather than a shallow summary.

## Package Contract

Create one folder per paper:

```text
<paper-id>/
  paper.md
  source_map.json
  translation_notes.md
  figure_table_cards.md
  mechanism_evidence_table.md
  dosage_window_table.md
  review_handoff.md
  obsidian_note.md
  visual_asset_spec.json
  assets/
    README.md
    asset_manifest.md
    visual_asset_report.json
    contact_sheet.png
    rendered_pages/
    figures/
    tables/
```

Use stable IDs across every file:

- `EX-###` for text excerpts, equations, methods, results, limitations, figure captions, and table notes.
- `F###-##` for figure cards.
- `T###-##` for table cards.
- `M###-##` for mechanism rows.
- `D###-##` for dosage-window rows.

Every interpretive sentence must cite at least one stable ID. If the source does not provide the needed page, number, image, standard, or method detail, write the gap with `[source missing]`, `[figure not provided]`, `[number not visible]`, or `[mechanism inferred, not directly proven]`.

## Required Products

`paper.md` is the readable intensive note. It should explain the paper identity, material system, research question, experiment matrix, key figure/table evidence, mechanism chain, limitations, and what can be borrowed for the user's WER-EA review.

`source_map.json` is the machine-readable anchor file. It must link every major claim to source location, excerpt, Chinese understanding, evidence layer, boundary, table destination, figure destination, and downstream file IDs.

`translation_notes.md` records translation choices, term normalization, sentence-level risk, and Chinese understanding for important excerpts. Use it to prevent literal translation, overclaiming, and accidental loss of method details.

`figure_table_cards.md` records figure/table cards and points to image assets when available. Figure cards should explain what the figure shows, what it can support, what it cannot support, and where it belongs in the review table/figure system.

`mechanism_evidence_table.md` separates direct evidence from inferred mechanism. For WER-EA, mechanism rows usually involve epoxy-amine curing, phase morphology, demulsification/film formation, storage stability, rheology, adhesion, moisture resistance, aging, fatigue, and service-condition evidence.

`dosage_window_table.md` records WER dosage, curing-agent ratio, emulsifier, SBR or other modifier dosage, asphalt/emulsion type, optimum range, overdose risk, construction window, and evidence boundary. If no dosage window is supported, say so explicitly.

`review_handoff.md` converts the paper into mini-review assets: literature-screening row, mechanism-evidence row, performance-comparison row, durability row, figure-planning notes, paragraph skeleton, safe synthesis sentence, and reviewer-risk warning.

`obsidian_note.md` is the user's Obsidian-facing note. Use the three-layer structure:

- `1 快读判断`
- `2 实验证据层`
- `3 写作转化层`

Include frontmatter, source status, concept links, graph links, and a reading-completion checklist. Concept links should point to knowledge nodes such as `[[水性环氧树脂]]`, `[[乳化沥青]]`, `[[三维网络结构]]`, `[[层间粘结性能]]`, `[[储存稳定性]]`, `[[FTIR]]`, `[[SEM]]`, `[[DSR]]`, `[[BBR]]`, or topic-specific equivalents. Do not create paper-title-only graph chains.

`visual_asset_spec.json` lists the PDF pages, crop boxes, asset IDs, claim boundaries, and figure/table destinations used to render and crop source visuals.

`assets/` stores cropped figures, rendered PDF pages, extracted tables, contact sheet, machine-readable report, and asset manifest. If an image/table asset cannot be generated, keep the failure reason in `assets/asset_manifest.md`, `assets/visual_asset_report.json`, and the matching `figure_table_cards.md` row.

## WER-EA Evidence Layers

Classify each source anchor into one or more layers:

| Evidence layer | What to capture | Common boundary |
|---|---|---|
| Material system | asphalt/emulsion type, WER, curing agent, emulsifier, SBR, fillers, substrate | Do not generalize across all WER-EA systems. |
| Preparation and construction | mixing, curing, demulsification, storage, viscosity, workability, coating | Lab preparation may not equal site construction. |
| Dosage window | optimum dosage, threshold, overdose effect, ratio, control group | Optimum is tied to the tested system and metric. |
| Performance | softening point, penetration, ductility, DSR, MSCR, BBR, pull-off, shear, waterproofing | Performance improvement is not mechanism proof. |
| Mechanism | FTIR, SEM, FM, AFM, DSC/TG, fluorescence, rheology, phase morphology | Morphology suggests structure; chemistry needs direct evidence. |
| Durability/service | water, freeze-thaw, aging, UV, acid/alkali, fatigue, traffic simulation, field | Lab durability does not prove field life. |
| Adjacent method | bonding test, AC/PCC interface, non-WER tack coat, method reference | Use as method evidence, not WER-EA material evidence. |

## Quality Bar

The package is not complete until:

- `source_map.json` is valid JSON.
- Every high-level claim in `paper.md`, `mechanism_evidence_table.md`, `dosage_window_table.md`, and `review_handoff.md` cites a stable ID.
- Figure/table cards state whether visual assets were actually inspected and include `visual_checked`, `asset_file`, `rendered_page_file`, `crop_status`, `defects`, and `qa_status`.
- `translation_notes.md` flags literal-translation and overclaim risks.
- `obsidian_note.md` has the three-layer structure and concept links.
- `assets/asset_manifest.md`, `assets/contact_sheet.png`, and `assets/visual_asset_report.json` exist when the source PDF is available.

## Safe Wording

Prefer bounded synthesis:

> The paper supports a binder-level mechanism interpretation that WER-EA performance depends on cured-network formation and formulation variables, but service durability should remain conditional unless interface, mixture, aging, and field evidence are also present.

Avoid:

> This figure proves WER-EA has excellent long-term pavement durability.
