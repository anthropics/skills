# Kong #258 — Academic Citation Version-Family Reconciliation

**Status:** prompt + sidecar contract implementation
**Date:** 2026-05-28
**Issue:** #258
**Scope:** Extend the v3.9.4 M5 version-family stub from institutional documents to academic citation chains such as arXiv preprint -> proceedings -> journal extension.

## Boundary

This patch is a faithfulness extension, not an autonomous correction layer.

- `literature_corpus_entry.schema.json` remains unchanged. It is adapter-owned and `additionalProperties: false`.
- `bibliography_agent.md` remains unchanged. Version discovery is owned by `timeline_extraction_agent`.
- `version_records.yaml` records candidate evidence and user-confirmed choices. It does not auto-standardize the reference list.
- `formatter_agent` and `draft_writer_agent` surface `VERSION_INCONSISTENT_CITATION` as an advisory, not a hard refusal.

## Sidecar

`phase2_investigation/version_records.yaml` is validated by
`shared/contracts/passport/version_records.schema.json`.

Minimal shape:

```yaml
schema_version: "1.0"
version_records:
  - version_family_id: attention-transformer-family
    canonical_slug: vaswani2017
    primary_version_key: attention-neurips-2017
    discovery_status: user_confirmed
    reconciliation_note: "Scholar selected proceedings as the primary citation."
    known_versions:
      - version_key: attention-arxiv-v1
        citation_key: vaswani2017-arxiv-v1
        kind: arxiv_preprint
        title: "Attention Is All You Need"
        year: 2017
        venue: "arXiv"
        doi: null
        arxiv_id: "1706.03762v1"
        url: "https://arxiv.org/abs/1706.03762v1"
        publication_date: {value: "2017-06", precision: month}
        metadata_provenance: arxiv_api
        source_locator: "arxiv:1706.03762v1"
        claim_scope_note: "Use only for claims verified against v1 text."
      - version_key: attention-neurips-2017
        citation_key: vaswani2017-neurips
        kind: proceedings
        title: "Attention Is All You Need"
        year: 2017
        venue: "NeurIPS 2017"
        doi: null
        arxiv_id: null
        url: "https://papers.nips.cc/paper/7181-attention-is-all-you-need"
        publication_date: {value: "2017", precision: year}
        metadata_provenance: user_override
        source_locator: "papers.nips.cc:7181"
        claim_scope_note: "Use for proceedings metadata and final citable record."
```

## Producer Protocol

`timeline_extraction_agent` writes candidate records from DOI/arXiv/title evidence:

1. For DOI-bearing entries, query Crossref and OpenAlex metadata when available.
2. For arXiv-bearing entries, query arXiv metadata for exact version IDs (`v1`, `v2`, etc.).
3. Group candidate records into `version_family_id` families only when evidence indicates the same work, not merely similar topic.
4. Mark the family `candidate` or `needs_review` until the scholar selects `primary_version_key`.
5. When the scholar confirms the selected citable version, mark `discovery_status: user_confirmed`.

## Consumer Protocol

When a cited slug joins a version family, `draft_writer_agent` and `formatter_agent` verify that all version-bound fields in the emitted claim are from the same `known_versions[]` entry:

- cited `year`
- visible venue / source label
- DOI, arXiv ID, URL
- direct quotation or anchor locator
- explicit version phrasing, such as "v1", "preprint", "conference version", or "journal extension"

If the fields mix versions, emit:

```text
VERSION_INCONSISTENT_CITATION: citation metadata, locator, or quoted claim mixes multiple records in version_family_id=<id>. Select one version or explicitly separate the claims.
```

This warning is advisory. The scholar decides whether to cite the preprint, proceedings, journal extension, or multiple versions explicitly.

## #127 Boundary

#127 handles the v3.10 triangulation policy layer: strict modes, `venue_type`, and terminal blocking when a reference is unmatched across indexes. #258 is narrower: it assumes the work exists and asks whether the metadata and quoted claim come from the same concrete version. Do not merge the two concerns:

- #127: "Does this reference meet policy for existence / venue classification?"
- #258: "Which concrete version of this existing work supports this citation?"
