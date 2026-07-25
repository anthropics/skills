# PDF Visual Asset Extraction

Use this reference when a WER-EA intensive-reading package needs nature-style PDF visual verification, rendered pages, cropped figures/tables, contact sheets, and asset manifests.

## Required Asset Layout

Each paper package must store PDF-derived visual assets under `assets/`:

```text
assets/
  README.md
  asset_manifest.md
  visual_asset_report.json
  contact_sheet.png
  rendered_pages/
    page_001.png
  figures/
    f015-01_fig-1-2.png
  tables/
    t015-01_tables-1-2.png
```

Do not copy the source PDF into the package. Treat the PDF as read-only source material and record only a sanitized `source_pdf_note`.

## Visual Asset Spec

Create `visual_asset_spec.json` in the paper folder before extraction:

```json
{
  "paper_id": "015-curing-agent-structure-wer-ea",
  "source_pdf_note": "WER-EA 30-paper set source PDF; not included in release",
  "assets": [
    {
      "asset_id": "F015-01",
      "kind": "figure",
      "paper_label": "Fig. 1-2",
      "source_page": 2,
      "crop_box": [0.05, 0.10, 0.95, 0.80],
      "claim_supported": "Epoxy-amine reaction and WER-EA crosslinking schematic.",
      "claim_too_strong": "The schematic alone proves performance improvement.",
      "destination": "mechanism map"
    }
  ]
}
```

`crop_box` may use relative page coordinates from 0 to 1 or rendered-page pixels as `[left, top, right, bottom]`. Prefer relative boxes for portable specs.

## Extraction Command

Use the bundled script:

```powershell
python skills\materials-reader\scripts\extract_pdf_visual_assets.py `
  --pdf <read-only-source.pdf> `
  --package-dir outputs\wer-ea-30-reading-sample\<paper-id> `
  --spec outputs\wer-ea-30-reading-sample\<paper-id>\visual_asset_spec.json `
  --dpi 220 `
  --json
```

The script renders selected pages, crops assets, writes `asset_manifest.md`, creates `contact_sheet.png`, and emits `visual_asset_report.json`.

## QA Rules

Every visual-checked card must record:

- `visual_checked`: `yes`, `partial`, or `no`.
- `source_pdf`: sanitized note only, not a local absolute path.
- `source_page`.
- `rendered_page_file`.
- `asset_file`.
- `crop_status`: `cropped`, `page-rendered-only`, or `failed`.
- `crop_box`.
- `defects`: `none` or a short defect note.
- `claim_boundary`: what the visual cannot prove.
- `qa_status`: `pass`, `partial`, or `fail`.

Use `partial` when the crop is useful but dense, small, or missing labels that need manual inspection. Never use a cropped morphology image as standalone proof of chemical mechanism or field durability.

## Dependency Boundary

The preferred runtime is PyMuPDF plus Pillow. If PyMuPDF is missing, the script must fail with an installation hint instead of fabricating assets. Poppler may be used manually, but this skill does not require it.
