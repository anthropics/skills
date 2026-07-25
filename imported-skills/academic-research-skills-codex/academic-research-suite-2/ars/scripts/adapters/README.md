# ARS Literature Corpus Adapters

Reference adapters that produce `literature_corpus[]` entries for the ARS Material Passport. Defined by the adapter contract at [`academic-pipeline/references/adapters/overview.md`](../../academic-pipeline/references/adapters/overview.md).

## What these are

Three starting-point adapters:

- **`folder_scan.py`** — scans a directory of files, parses citation metadata from filenames.
- **`zotero.py`** — reads a Better BibTeX JSON export.
- **`obsidian.py`** — reads an Obsidian vault (frontmatter Convention A or Karpathy-style Convention B).

Each writes two files: a `passport.yaml` with `literature_corpus[]` entries, and a `rejection_log.yaml` listing whatever the adapter could not map onto a valid entry.

**These are references, not products.** If your corpus is in Zotero, Obsidian, or a plain folder, you can run these directly; if it is in Notion, Readwise, Airtable, a custom SQLite, etc., copy a reference adapter and adapt it to your source.

## Running a reference adapter

### folder_scan

```bash
python scripts/adapters/folder_scan.py \
    --input /path/to/your/pdf/folder \
    --passport /tmp/passport.yaml \
    --rejection-log /tmp/rejection_log.yaml
```

Filenames are parsed with two conventions plus a fallback: `{Family}_{Year}_{title}.{ext}`, `{Family}{Year}{title}.{ext}`, or `... {Year} ... {Family} ...`. Files whose filename cannot yield both a family and a year are rejected. Non-ASCII filenames are rejected (Unicode support is a deferred extension). Symlinks are followed but the rejection log records the un-resolved path so collisions across subdirectories remain distinguishable.

### zotero

Export your Zotero library as **Better BibTeX JSON** (Zotero → File → Export Library → Format: Better CSL JSON, with the Better BibTeX extension installed). Then:

```bash
python scripts/adapters/zotero.py \
    --input ~/zotero_export.json \
    --passport /tmp/passport.yaml \
    --rejection-log /tmp/rejection_log.yaml
```

This adapter does NOT call the Zotero Web API. If you want live sync, write your own adapter using this file as a starting point. Items missing required fields (`title`, `authors`, parseable `year`, `source_pointer`) are rejected with a categorical reason; seasonal dates like `Spring 2024` are rejected as `year_unparseable`.

### obsidian

```bash
python scripts/adapters/obsidian.py \
    --input ~/ObsidianVault \
    --passport /tmp/passport.yaml \
    --rejection-log /tmp/rejection_log.yaml
```

Files under `_templates/` and `.obsidian/` are skipped. Wikilinks (`[[other note]]`) are NOT resolved; they appear as literal text in `user_notes`. Notes with valid YAML frontmatter use Convention A (BibTeX-style: `citekey:`, `authors:`, `year:`, `title:`); notes without frontmatter fall through to Convention B (filename stem as citation_key, body as user_notes). Notes with malformed YAML frontmatter are rejected as `invalid_field_format` rather than silently re-classified as Convention B.

## Validating adapter output

Before using the passport in any ARS workflow:

```bash
python scripts/check_literature_corpus_schema.py \
    --passport /tmp/passport.yaml \
    --rejection-log /tmp/rejection_log.yaml
```

## How to write your own adapter

1. Read the adapter contract at [`academic-pipeline/references/adapters/overview.md`](../../academic-pipeline/references/adapters/overview.md).
2. Read the JSON schemas:
   - [`shared/contracts/passport/literature_corpus_entry.schema.json`](../../shared/contracts/passport/literature_corpus_entry.schema.json)
   - [`shared/contracts/passport/rejection_log.schema.json`](../../shared/contracts/passport/rejection_log.schema.json)
3. Copy one of `folder_scan.py` / `zotero.py` / `obsidian.py` as a starting point.
4. Change the input-reading and field-mapping code for your source.
5. Keep the output shape exactly (sorted `literature_corpus[]` by `citation_key`, always emit `rejection_log.yaml`, schema-clean entries only).
6. Set `obtained_via: "other"` and `adapter_name: "<your-adapter-name>"` on every entry you produce.
7. Reuse helpers in [`_common.py`](_common.py) where possible — `make_citation_key`, `ensure_unique_citekey`, `parse_csl_name`, `parse_semicolon_names`, `path_to_file_uri`, `write_passport`, `write_rejection_log`, `now_iso`. They encode the contract details so you do not have to re-derive them.
8. Validate: `python scripts/check_literature_corpus_schema.py --passport <your passport>`.
9. Write tests modeled on `scripts/adapters/tests/`. The conftest fixtures `clean_timestamps` and `load_yaml` make golden-output testing easy.

## Privacy reminder

`abstract` and `user_notes` can contain publisher-copyrighted material. Before sharing a passport that contains these fields publicly (e.g., in a public repo or over the web), make sure you have the right to publish that text. ARS does not enforce this — it only warns you in the schema description.

## Tests

```bash
cd <repo_root>
pytest scripts/adapters/tests/ -v
```

CI runs these on every push / PR that touches `scripts/adapters/**`, `shared/contracts/passport/**`, the adapter overview, or either of the two lint scripts.
