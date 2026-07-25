# Adapter Contract — Producing `literature_corpus[]` Entries

**Status**: Stable as of ARS v3.6.4
**Applies to**: any adapter that produces a Material Passport `literature_corpus[]` field
**Authoritative schemas**:
- [`shared/contracts/passport/literature_corpus_entry.schema.json`](../../../shared/contracts/passport/literature_corpus_entry.schema.json)
- [`shared/contracts/passport/rejection_log.schema.json`](../../../shared/contracts/passport/rejection_log.schema.json)

## 1. What an adapter is

An **adapter** is a program (in any language) that reads a user-owned corpus source — a Zotero export, an Obsidian vault, a folder of PDFs, a Notion database, a custom SQLite library — and produces:

1. **`passport.yaml`** with a top-level `literature_corpus` array conforming to `literature_corpus_entry.schema.json`.
2. **`rejection_log.yaml`** conforming to `rejection_log.schema.json`, always emitted (empty when no rejections).

ARS provides three Python reference adapters in [`scripts/adapters/`](../../../scripts/adapters/). Users are expected to write their own adapters for non-reference sources. The three reference adapters are starting points, not production tools.

## 2. Why a contract, not a plugin API

ARS deliberately does NOT run adapter code itself. The adapter runs in the user's environment, reads the user's data, and emits YAML files. ARS reads those YAML files. Rationale:

- Each corpus source (Zotero, Obsidian, custom) has its own versioning, auth, and data quirks. Pinning one plugin API would force ARS to track all of them.
- Keeping the boundary at "YAML files on disk" means a user can use any language, any scheduling mechanism, and any privacy posture without touching ARS internals.
- ARS remains a writing/review-layer tool; corpus integration stays in user-owned code.

## 3. Entry field reference

Refer to the [`literature_corpus_entry` schema](../../../shared/contracts/passport/literature_corpus_entry.schema.json) for the authoritative contract. The field tables below are generated from that schema and must not drift.

<!-- GENERATED:LITERATURE_CORPUS_REQUIRED:START -->
| Field | Type | Description (first sentence) |
|---|---|---|
| `authors` | array | CSL-JSON name format. |
| `citation_key` | string | Stable unique identifier for this entry within the passport. |
| `source_pointer` | string | Stable URI locating this work in the user's own KB. |
| `title` | string | — |
| `year` | integer | Publication year. |
<!-- GENERATED:LITERATURE_CORPUS_REQUIRED:END -->

<!-- GENERATED:LITERATURE_CORPUS_OPTIONAL:START -->
| Field | Type | Description (first sentence) |
|---|---|---|
| `abstract` | string | PRIVATE FIELD. |
| `adapter_name` | string | Optional. |
| `adapter_version` | string | — |
| `arxiv_id` | string | Optional arXiv identifier for arXiv-hosted works. |
| `contamination_signals` | object | v3.7.3 + v3.9.0 + v3.11 contaminated-source advisory field (spec v3.7.3 §3.2 + v3.9.0 §3.4–§3.5 + v3.11 #182 Delta 1). |
| `contamination_signals_backfilled_at` | string | v3.7.3 backfill provenance (issue #105). |
| `description_last_audit` | null \| string | v3.7.1 trust-chain field. |
| `description_source` | string | v3.7.1 trust-chain field. |
| `doi` | string | DOI without leading 'doi:' or URL prefix. |
| `obtained_at` | string | Strongly recommended. |
| `obtained_via` | string | Strongly recommended. |
| `source_acquired` | boolean | v3.7.1 trust-chain field (spec § 3.1, D1). |
| `source_acquisition_date` | string | v3.7.1 trust-chain field. |
| `source_acquisition_path` | string | v3.7.1 trust-chain field. |
| `source_verification_method` | string | v3.7.1 trust-chain field. |
| `source_verified_against_original` | boolean | v3.7.1 trust-chain field. |
| `tags` | array | User-assigned tags from the source KB. |
| `user_notes` | string | PRIVATE FIELD. |
| `venue` | string | — |
| `venue_type` | string | v3.10 (spec §3 PR-B item 2). |
| `venue_type_provenance` | string | v3.10 (spec §3 PR-B item 3). |
| `venue_type_source` | string | v3.10 (spec §3 PR-B item 4). |
<!-- GENERATED:LITERATURE_CORPUS_OPTIONAL:END -->

### 3.1 `authors` format (CSL-JSON names)

Each entry in `authors[]` is one of:

- **Personal name**: `{family: "Chen", given: "Cindy"}`. `family` is required; `given` and CSL particles (`suffix`, `dropping-particle`, `non-dropping-particle`, `comma-suffix`, `static-ordering`, `parse-names`) are optional.
- **Institution / corporate name**: `{literal: "World Health Organization"}`. `literal` is required; no other fields.

Adapters SHOULD preserve the upstream distinction (personal vs. institution). See [CSL-JSON name spec](https://docs.citationstyles.org/en/stable/specification.html#names) for edge cases.

### 3.2 Privacy caveat for `abstract` and `user_notes`

Publishers typically retain rights to abstracts; user notes often quote copyrighted material. The schema marks these fields as PRIVATE and does NOT enforce anything at the CI level. **If you publish a passport (e.g., commit it to a public repo or share it on the web), you are responsible for removing or clearing these fields.** ARS consumers treat both fields as optional; omitting them never causes failure.

## 4. Rejection log

Whenever an adapter cannot produce a valid `literature_corpus_entry` for an input item, it MUST push a rejection into `rejection_log.yaml.rejected[]` and MUST NOT silently drop the item.

The `reason` field uses a closed enum of categorical values:

| `reason` | When |
|----------|------|
| `missing_required_field` | One or more required fields (citation_key / title / authors / year / source_pointer) cannot be derived. Adapter SHOULD also populate `missing_fields`. |
| `invalid_field_format` | A field is present but fails schema format (e.g., DOI pattern mismatch). |
| `duplicate_citation_key` | Another entry already used this citekey and the adapter cannot disambiguate. |
| `unresolvable_source_pointer` | The source URI points to something that does not exist. Adapters typically do not check this; use only if the adapter actually tries to resolve. |
| `year_unparseable` | Year cannot be extracted from the source field ("n.d.", "forthcoming", "Spring 2024"). |
| `authors_unparseable` | Authors field is empty, contains only non-author creators, or has unparseable content. |
| `adapter_error` | Adapter-internal bug, not an input data problem. Use sparingly. |
| `other` | Anything else. When `reason=other`, `detail` is REQUIRED. |

The `raw` field, when present, MUST be either an object (structured input) or a string (filename or text line). Arrays, numbers, booleans, and null are disallowed so downstream viewers can assume printable shapes.

## 5. Error handling (fail-soft)

**Entry-level problems** → push to rejection log, continue.
**Adapter-level problems** (input file missing, unreadable, malformed at the root) → write nothing, print a clear error to stderr, exit with code 1.

Do NOT emit a partial passport. Either the passport represents a complete scan of the user's input, or the adapter failed loudly.

## 6. Determinism

Running an adapter twice on identical input MUST produce byte-identical output except for:

- `generated_at` in the rejection log
- `obtained_at` on each entry

Achieve this by:

- Sorting `literature_corpus[]` by `citation_key`
- Sorting `rejection_log.rejected[]` by `source`
- Serializing YAML with sorted keys

## 7. Provenance

Each `literature_corpus` entry SHOULD carry `obtained_via` and `obtained_at`. The `rejection_log` MUST carry `adapter_name`, `adapter_version`, and `generated_at`. These fields let downstream users trace which adapter version produced which entry — useful when a library's schema or a source KB layout changes.

## 8. Extension points for user-written adapters

Custom adapters are welcome and expected. Recommended conventions:

- Set `obtained_via: "other"` on each entry, and set `adapter_name` to a clear string (e.g., `"notion-adapter-v1"`, `"my-custom-sqlite-reader"`).
- Set `adapter_version` to a semver-ish string so downstream tools can diagnose output changes.
- Follow the same CLI shape as the three reference adapters (`--input`, `--passport`, `--rejection-log`) if you want to slot into similar tooling.

Common user-written adapter families include:

- **Zotero Web API**: one that calls `api.zotero.org` with a user API token. Not shipped with ARS by design (auth and rate-limit management would pull ARS into data-layer territory).
- **Notion / Readwise / Airtable**: each has its own SDK; the adapter's job is only to map the source's book/article objects into `literature_corpus_entry` shape.
- **Cross-source merger**: reads multiple sources and emits a combined passport. Handle citekey collisions explicitly.

## 9. Testing your adapter

Before committing passport output to any workflow:

1. Validate against the schema: `python scripts/check_literature_corpus_schema.py --passport <your_passport.yaml> --rejection-log <your_rejection_log.yaml>`.
2. Run your adapter twice on the same input and diff the outputs (after stripping `generated_at` / `obtained_at`). Any non-timestamp difference is a determinism bug.
3. Feed a known-bad entry to confirm it lands in the rejection log rather than silently vanishing or crashing.

The three reference adapters have pytest coverage under `scripts/adapters/tests/` — copying that pattern for your own adapter is a good starting point.

## 10. Relationship to other ARS artifacts

- [`shared/handoff_schemas.md`](../../../shared/handoff_schemas.md) Schema 9: the `literature_corpus[]` field lives inside the Material Passport.
- [`academic-pipeline/references/passport_as_reset_boundary.md`](../passport_as_reset_boundary.md): `literature_corpus[]` is consumed across reset boundaries like any other passport field.
- ARS agents that consume `literature_corpus[]` are **deferred** to v3.6.5+. As of v3.6.4, the field is a defined input port with no runtime consumer; adapters produce it, future ARS versions read it.
