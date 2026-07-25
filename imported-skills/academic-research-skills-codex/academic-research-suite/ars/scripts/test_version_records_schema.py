"""Tests for Kong #258 version_records sidecar schema."""
from __future__ import annotations

from pathlib import Path

import jsonschema
import pytest

from tests.test_helpers import load_json_schema


REPO_ROOT = Path(__file__).resolve().parents[1]
SCHEMAS = REPO_ROOT / "shared/contracts/passport"


def _schema(name: str) -> dict:
    return load_json_schema(SCHEMAS / name)


def _valid_version_records() -> dict:
    return {
        "schema_version": "1.0",
        "version_records": [
            {
                "version_family_id": "attention-transformer-family",
                "canonical_slug": "vaswani2017",
                "primary_version_key": "attention-neurips-2017",
                "discovery_status": "user_confirmed",
                "reconciliation_note": "Scholar selected proceedings as the primary rendered citation.",
                "known_versions": [
                    {
                        "version_key": "attention-arxiv-v1",
                        "citation_key": "vaswani2017-arxiv-v1",
                        "kind": "arxiv_preprint",
                        "title": "Attention Is All You Need",
                        "year": 2017,
                        "venue": "arXiv",
                        "doi": None,
                        "arxiv_id": "1706.03762v1",
                        "url": "https://arxiv.org/abs/1706.03762v1",
                        "publication_date": {"value": "2017-06", "precision": "month"},
                        "metadata_provenance": "arxiv_api",
                        "source_locator": "arxiv:1706.03762v1",
                        "claim_scope_note": "Use only for claims verified against the v1 preprint text.",
                        "notes": None,
                    },
                    {
                        "version_key": "attention-neurips-2017",
                        "citation_key": "vaswani2017-neurips",
                        "kind": "proceedings",
                        "title": "Attention Is All You Need",
                        "year": 2017,
                        "venue": "NeurIPS 2017",
                        "doi": None,
                        "arxiv_id": None,
                        "url": "https://papers.nips.cc/paper/7181-attention-is-all-you-need",
                        "publication_date": {"value": "2017", "precision": "year"},
                        "metadata_provenance": "user_override",
                        "source_locator": "papers.nips.cc:7181",
                        "claim_scope_note": "Use for proceedings metadata and final citable record.",
                        "notes": None,
                    },
                ],
            }
        ],
    }


def test_version_records_schema_validates_canonical_example():
    jsonschema.validate(_valid_version_records(), _schema("version_records.schema.json"))


def test_version_records_rejects_unknown_top_level_field():
    bad = _valid_version_records()
    bad["literature_corpus_patch"] = []
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad, _schema("version_records.schema.json"))


def test_version_records_rejects_invalid_arxiv_id():
    bad = _valid_version_records()
    bad["version_records"][0]["known_versions"][0]["arxiv_id"] = "arXiv:1706.03762v1"
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad, _schema("version_records.schema.json"))


def _drop_top_schema_version(doc: dict) -> dict:
    del doc["schema_version"]
    return doc


def _drop_record_required(doc: dict) -> dict:
    del doc["version_records"][0]["discovery_status"]
    return doc


def _empty_known_versions(doc: dict) -> dict:
    doc["version_records"][0]["known_versions"] = []
    return doc


def _drop_known_version_required(doc: dict) -> dict:
    del doc["version_records"][0]["known_versions"][0]["metadata_provenance"]
    return doc


def _bad_discovery_status(doc: dict) -> dict:
    doc["version_records"][0]["discovery_status"] = "maybe"
    return doc


def _bad_kind(doc: dict) -> dict:
    doc["version_records"][0]["known_versions"][0]["kind"] = "blog_post"
    return doc


def _bad_metadata_provenance(doc: dict) -> dict:
    doc["version_records"][0]["known_versions"][0]["metadata_provenance"] = "vibes"
    return doc


def _empty_title(doc: dict) -> dict:
    doc["version_records"][0]["known_versions"][0]["title"] = ""
    return doc


def _extra_prop_on_record(doc: dict) -> dict:
    doc["version_records"][0]["surprise"] = True
    return doc


def _extra_prop_on_known_version(doc: dict) -> dict:
    doc["version_records"][0]["known_versions"][0]["surprise"] = True
    return doc


def _bad_date_precision(doc: dict) -> dict:
    doc["version_records"][0]["known_versions"][0]["publication_date"] = {
        "value": "2017-06",
        "precision": "fortnight",
    }
    return doc


@pytest.mark.parametrize(
    "mutator",
    [
        _drop_top_schema_version,
        _drop_record_required,
        _empty_known_versions,
        _drop_known_version_required,
        _bad_discovery_status,
        _bad_kind,
        _bad_metadata_provenance,
        _empty_title,
        _extra_prop_on_record,
        _extra_prop_on_known_version,
        _bad_date_precision,
    ],
)
def test_version_records_rejects_mutations(mutator):
    """Each mutation of the canonical valid doc must fail validation.

    Guards against the schema silently relaxing a constraint: required fields,
    minItems on known_versions, the discovery_status / kind / metadata_provenance
    enums, non-empty title, additionalProperties:false at each level, and date
    precision enum. Year bounds are covered separately below.
    """
    bad = mutator(_valid_version_records())
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad, _schema("version_records.schema.json"))


@pytest.mark.parametrize("year", [999, 2101])
def test_version_records_rejects_year_out_of_range(year):
    """year must stay within the schema's minimum/maximum (1000-2100)."""
    bad = _valid_version_records()
    bad["version_records"][0]["known_versions"][0]["year"] = year
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad, _schema("version_records.schema.json"))


def test_literature_corpus_entry_contract_remains_unmodified_for_version_families():
    """Kong #258 keeps version-family data in sidecar, not literature_corpus_entry."""
    literature_schema = _schema("literature_corpus_entry.schema.json")
    props = literature_schema["properties"]
    assert "version_family_id" not in props
    assert "version_records" not in props


def test_kong_258_agent_and_formatter_markers_present():
    timeline_agent = (REPO_ROOT / "deep-research/agents/timeline_extraction_agent.md").read_text()
    draft_writer = (REPO_ROOT / "academic-paper/agents/draft_writer_agent.md").read_text()
    formatter = (REPO_ROOT / "academic-paper/agents/formatter_agent.md").read_text()

    assert "## Academic Citation Version Discovery (Kong #258)" in timeline_agent
    assert "phase2_investigation/version_records.yaml" in timeline_agent
    assert "## Citation Version-Family Check (Kong #258)" in draft_writer
    assert "VERSION_INCONSISTENT_CITATION" in draft_writer
    assert "## Citation Version-Family Advisory (Kong #258)" in formatter
    assert "VERSION_INCONSISTENT_CITATION" in formatter


def test_kong_258_design_doc_documents_127_boundary_and_example_exists():
    design = (REPO_ROOT / "docs/design/2026-05-28-kong-258-version-family-reconciliation.md").read_text()
    example = REPO_ROOT / "academic-paper/examples/version_family_reconciliation_example.md"
    assert "#127 Boundary" in design
    assert "literature_corpus_entry.schema.json" in design
    assert "remains unchanged" in design
    assert "VERSION_INCONSISTENT_CITATION" in design
    assert example.exists()
