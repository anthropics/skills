# Version-Family Reconciliation Example (Kong #258)

This example shows how ARS surfaces a citation-version mismatch without auto-correcting the manuscript.

## Scenario

The author wants to cite *Attention Is All You Need*. Their corpus contains two concrete versions:

- arXiv preprint v1
- NeurIPS 2017 proceedings record

The scholar selects the proceedings record as the primary citable version, but the draft sentence quotes the arXiv v1 locator while the reference list renders proceedings metadata.

## Sidecar

`phase2_investigation/version_records.yaml`:

```yaml
schema_version: "1.0"
version_records:
  - version_family_id: attention-transformer-family
    canonical_slug: vaswani2017
    primary_version_key: attention-neurips-2017
    discovery_status: user_confirmed
    reconciliation_note: "Proceedings record selected as default citation; arXiv v1 can be cited explicitly for preprint-specific claims."
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
        claim_scope_note: "Use only for text verified against the v1 preprint."
        notes: null
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
        claim_scope_note: "Use for proceedings metadata and the final citable record."
        notes: null
```

## Problem Draft

```markdown
The preprint v1 states the Transformer architecture relies entirely on attention mechanisms (Vaswani et al., 2017).<!--ref:vaswani2017-neurips ok--><!--anchor:section:arxiv:1706.03762v1:sec3-->
```

The citation slug points to the proceedings record, but the prose and anchor point to arXiv v1.

## Advisory

```text
VERSION_INCONSISTENT_CITATION: citation metadata, locator, or quoted claim mixes multiple records in version_family_id=attention-transformer-family. The rendered slug vaswani2017-neurips belongs to attention-neurips-2017, while the prose/anchor refers to attention-arxiv-v1. Select one version or explicitly separate the claims.
```

## Acceptable Fix A — Cite the Preprint Explicitly

```markdown
The arXiv v1 preprint states the Transformer architecture relies entirely on attention mechanisms (Vaswani et al., 2017).<!--ref:vaswani2017-arxiv-v1 ok--><!--anchor:section:arxiv:1706.03762v1:sec3-->
```

## Acceptable Fix B — Use the Proceedings Record

```markdown
The proceedings version presents the Transformer architecture as relying entirely on attention mechanisms (Vaswani et al., 2017).<!--ref:vaswani2017-neurips ok--><!--anchor:section:papers.nips.cc:7181:sec3-->
```

## Acceptable Fix C — Compare Versions Explicitly

```markdown
The arXiv v1 preprint and the NeurIPS proceedings version both frame the Transformer as an attention-only architecture, but the manuscript cites the proceedings version as the primary record (Vaswani et al., 2017).<!--ref:vaswani2017-arxiv-v1 ok--><!--anchor:section:arxiv:1706.03762v1:sec3--><!--ref:vaswani2017-neurips ok--><!--anchor:section:papers.nips.cc:7181:sec3-->
```

The important rule is that each version-bound claim has its own slug and locator. ARS does not decide which version is "better"; the scholar selects the version appropriate to the claim.
