"""Validates literature_corpus_entry.schema.json self-consistency and
round-trips a known-good example entry against it."""
from pathlib import Path
import json
import pytest
from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "shared/contracts/passport/literature_corpus_entry.schema.json"


def _load_schema():
    with SCHEMA_PATH.open("r", encoding="utf-8") as f:
        return json.load(f)


def _validator(schema):
    """Validator with format_checker so format-keyword constraints
    (e.g. date-time on obtained_at) are actually enforced."""
    return Draft202012Validator(
        schema, format_checker=Draft202012Validator.FORMAT_CHECKER
    )


def test_schema_file_exists():
    assert SCHEMA_PATH.exists(), f"schema missing at {SCHEMA_PATH}"


def test_schema_is_valid_draft_2020_12():
    schema = _load_schema()
    Draft202012Validator.check_schema(schema)


def test_required_set_matches_spec():
    schema = _load_schema()
    assert schema["required"] == [
        "citation_key",
        "title",
        "authors",
        "year",
        "source_pointer",
    ]


def test_additional_properties_is_false():
    schema = _load_schema()
    assert schema["additionalProperties"] is False


def test_valid_personal_author_entry_passes():
    schema = _load_schema()
    entry = {
        "citation_key": "chen2024ai",
        "title": "AI assessment",
        "authors": [{"family": "Chen", "given": "Cindy"}],
        "year": 2024,
        "source_pointer": "https://doi.org/10.1234/xyz",
    }
    _validator(schema).validate(entry)


def test_valid_institution_author_entry_passes():
    schema = _load_schema()
    entry = {
        "citation_key": "who2024report",
        "title": "World report",
        "authors": [{"literal": "World Health Organization"}],
        "year": 2024,
        "source_pointer": "https://www.who.int/report",
    }
    _validator(schema).validate(entry)


def test_missing_required_field_fails():
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = {
        "citation_key": "chen2024ai",
        "title": "AI assessment",
        # missing authors
        "year": 2024,
        "source_pointer": "file:///x.pdf",
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


def test_author_must_be_either_personal_or_literal():
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = {
        "citation_key": "bad2024",
        "title": "Bad author",
        "authors": [{}],  # neither family nor literal
        "year": 2024,
        "source_pointer": "file:///x.pdf",
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


def test_year_out_of_range_fails():
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = {
        "citation_key": "old1",
        "title": "Ancient",
        "authors": [{"family": "X"}],
        "year": 999,
        "source_pointer": "file:///x.pdf",
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


def test_citation_key_pattern_rejects_leading_digit():
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = {
        "citation_key": "2024chen",
        "title": "T",
        "authors": [{"family": "C"}],
        "year": 2024,
        "source_pointer": "file:///x.pdf",
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


def test_additional_property_fails():
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = {
        "citation_key": "chen2024",
        "title": "T",
        "authors": [{"family": "C"}],
        "year": 2024,
        "source_pointer": "file:///x.pdf",
        "custom_field": "should_not_be_allowed",
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


def test_obtained_via_enum_constrained():
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = {
        "citation_key": "chen2024",
        "title": "T",
        "authors": [{"family": "C"}],
        "year": 2024,
        "source_pointer": "file:///x.pdf",
        "obtained_via": "rubber-duck",
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


def test_obtained_via_other_without_adapter_name_fails():
    """Spec §obtained_via: 'Required when obtained_via=other'.
    Schema MUST enforce this conditionally, not via prose only."""
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = {
        "citation_key": "chen2024",
        "title": "T",
        "authors": [{"family": "C"}],
        "year": 2024,
        "source_pointer": "file:///x.pdf",
        "obtained_via": "other",
        # adapter_name missing — must fail
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


def test_obtained_via_other_with_adapter_name_passes():
    schema = _load_schema()
    entry = {
        "citation_key": "chen2024",
        "title": "T",
        "authors": [{"family": "C"}],
        "year": 2024,
        "source_pointer": "file:///x.pdf",
        "obtained_via": "other",
        "adapter_name": "my-custom-adapter",
    }
    _validator(schema).validate(entry)


def test_obtained_via_known_value_does_not_require_adapter_name():
    """Conditional only fires for 'other'. Reference adapters
    (zotero-bbt-export, obsidian-vault, folder-scan) must validate
    without adapter_name."""
    schema = _load_schema()
    entry = {
        "citation_key": "chen2024",
        "title": "T",
        "authors": [{"family": "C"}],
        "year": 2024,
        "source_pointer": "file:///x.pdf",
        "obtained_via": "folder-scan",
    }
    _validator(schema).validate(entry)


def test_invalid_obtained_at_format_fails():
    """obtained_at: format=date-time must be enforced. Without
    format_checker the keyword is silently ignored."""
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = {
        "citation_key": "chen2024",
        "title": "T",
        "authors": [{"family": "C"}],
        "year": 2024,
        "source_pointer": "file:///x.pdf",
        "obtained_at": "not-a-date",
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


def test_valid_obtained_at_format_passes():
    schema = _load_schema()
    entry = {
        "citation_key": "chen2024",
        "title": "T",
        "authors": [{"family": "C"}],
        "year": 2024,
        "source_pointer": "file:///x.pdf",
        "obtained_at": "2026-04-25T10:30:00Z",
    }
    _validator(schema).validate(entry)


def test_valid_arxiv_id_passes():
    schema = _load_schema()
    entry = {
        "citation_key": "chen2024",
        "title": "T",
        "authors": [{"family": "C"}],
        "year": 2024,
        "source_pointer": "https://arxiv.org/abs/2401.12345",
        "arxiv_id": "2401.12345",
    }
    _validator(schema).validate(entry)


def test_valid_legacy_arxiv_id_passes():
    schema = _load_schema()
    entry = {
        "citation_key": "niels1997",
        "title": "Legacy arXiv",
        "authors": [{"family": "Niels"}],
        "year": 1997,
        "source_pointer": "https://arxiv.org/abs/hep-th/9711200",
        "arxiv_id": "hep-th/9711200",
    }
    _validator(schema).validate(entry)


def test_invalid_arxiv_id_rejected():
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = {
        "citation_key": "invalid2024",
        "title": "Bad arXiv",
        "authors": [{"family": "C"}],
        "year": 2024,
        "source_pointer": "https://arxiv.org/abs/2401.12345",
        "arxiv_id": "arXiv:2401.12345",
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


def test_valid_legacy_arxiv_id_with_version_passes():
    schema = _load_schema()
    entry = {
        "citation_key": "hepth1997v2",
        "title": "Legacy arXiv versioned",
        "authors": [{"family": "C"}],
        "year": 1997,
        "source_pointer": "https://arxiv.org/abs/hep-th/9711200v2",
        "arxiv_id": "hep-th/9711200v2",
    }
    _validator(schema).validate(entry)


def test_valid_legacy_arxiv_id_with_subject_class_passes():
    schema = _load_schema()
    entry = {
        "citation_key": "math0703087",
        "title": "Subject-class arXiv",
        "authors": [{"family": "C"}],
        "year": 2007,
        "source_pointer": "https://arxiv.org/abs/math.AG/0703087",
        "arxiv_id": "math.AG/0703087",
    }
    _validator(schema).validate(entry)


def test_valid_short_new_style_arxiv_id_passes():
    schema = _load_schema()
    entry = {
        "citation_key": "smallid0704",
        "title": "Short new-style arXiv",
        "authors": [{"family": "C"}],
        "year": 2007,
        "source_pointer": "https://arxiv.org/abs/0704.0001",
        "arxiv_id": "0704.0001",
    }
    _validator(schema).validate(entry)


def test_arxiv_id_is_optional():
    schema = _load_schema()
    entry = {
        "citation_key": "chen2024opt",
        "title": "Optional arXiv ID",
        "authors": [{"family": "C"}],
        "year": 2024,
        "source_pointer": "https://doi.org/10.1234/xyz",
    }
    _validator(schema).validate(entry)


# --- v3.7.3 contamination_signals (L3-2) -------------------------------
# Motivation: Zhao et al. arXiv:2605.07723 (2026-05).

def _base_entry():
    return {
        "citation_key": "chen2024",
        "title": "T",
        "authors": [{"family": "C"}],
        "year": 2024,
        "source_pointer": "file:///x.pdf",
    }


def test_contamination_signals_absent_is_valid():
    """v3.7.3: contamination_signals is optional; legacy entries stay valid."""
    schema = _load_schema()
    _validator(schema).validate(_base_entry())


def test_contamination_signals_empty_object_is_valid():
    """Both sub-fields optional within the object."""
    schema = _load_schema()
    entry = _base_entry() | {"contamination_signals": {}}
    _validator(schema).validate(entry)


def test_contamination_signals_both_false_is_valid():
    """Computed and no contamination evidence."""
    schema = _load_schema()
    entry = _base_entry() | {
        "contamination_signals": {
            "preprint_post_llm_inflection": False,
            "semantic_scholar_unmatched": False,
        }
    }
    _validator(schema).validate(entry)


def test_contamination_signals_both_true_is_valid():
    """Maximum contamination — still valid; advisory not blocking."""
    schema = _load_schema()
    entry = _base_entry() | {
        "contamination_signals": {
            "preprint_post_llm_inflection": True,
            "semantic_scholar_unmatched": True,
        }
    }
    _validator(schema).validate(entry)


def test_contamination_signals_unknown_subfield_rejected():
    """additionalProperties: false on contamination_signals."""
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = _base_entry() | {
        "contamination_signals": {"unknown_signal": True}
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


def test_contamination_signals_non_boolean_rejected():
    """Sub-fields are strict booleans, not truthy strings."""
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = _base_entry() | {
        "contamination_signals": {"preprint_post_llm_inflection": "yes"}
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


# --- v3.7.3 gemini review F5 closure: year < 2024 cross-field rule -----

def test_preprint_flag_true_with_year_before_2024_rejected():
    """v3.7.3 F5: setting preprint_post_llm_inflection=true with year<2024
    is logically contradictory and schema must reject it."""
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = _base_entry() | {
        "year": 2022,
        "contamination_signals": {"preprint_post_llm_inflection": True},
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


def test_preprint_flag_true_with_year_2024_passes():
    """v3.7.3 F5: year=2024 (the threshold) + flag=true is valid."""
    schema = _load_schema()
    entry = _base_entry() | {
        "year": 2024,
        "contamination_signals": {"preprint_post_llm_inflection": True},
    }
    _validator(schema).validate(entry)


def test_preprint_flag_false_with_pre_2024_year_passes():
    """v3.7.3 F5: reverse direction is legal — pre-2024 entries can
    have flag=false (e.g., they computed the signal and found no
    contamination because the venue is not a preprint server)."""
    schema = _load_schema()
    entry = _base_entry() | {
        "year": 2020,
        "contamination_signals": {"preprint_post_llm_inflection": False},
    }
    _validator(schema).validate(entry)


def test_preprint_flag_absent_with_pre_2024_year_passes():
    """v3.7.3 F5: cross-field rule only fires when flag is true.
    Absent flag = signal not computed; pre-2024 year still valid."""
    schema = _load_schema()
    entry = _base_entry() | {"year": 2020}
    _validator(schema).validate(entry)


# --- v3.7.3 codex round-3 F11 closure: manual-entry exemption ----------

def test_manual_entry_with_ss_unmatched_field_rejected():
    """v3.7.3 F11: obtained_via=manual + semantic_scholar_unmatched
    present is a contract violation — bibliography_agent SKIPS the
    Semantic Scholar check on user-curated entries and OMITS the
    field. Schema must reject either true or false on manual."""
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = _base_entry() | {
        "obtained_via": "manual",
        "contamination_signals": {"semantic_scholar_unmatched": True},
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


def test_manual_entry_with_ss_unmatched_false_also_rejected():
    """v3.7.3 F11: even semantic_scholar_unmatched=false on a manual
    entry is wrong — the field MUST be absent, since 'false' would
    imply 'checked and found' which contradicts the skip-the-check
    exemption."""
    from jsonschema.exceptions import ValidationError
    schema = _load_schema()
    entry = _base_entry() | {
        "obtained_via": "manual",
        "contamination_signals": {"semantic_scholar_unmatched": False},
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(entry)


def test_manual_entry_with_only_preprint_flag_passes():
    """v3.7.3 F11: manual entries CAN still set
    preprint_post_llm_inflection (the year+venue check doesn't
    depend on the SS API), they just can't carry the unmatched
    field. preprint_post_llm_inflection=true is allowed when
    year>=2024 per F5."""
    schema = _load_schema()
    entry = _base_entry() | {
        "year": 2024,
        "obtained_via": "manual",
        "contamination_signals": {"preprint_post_llm_inflection": True},
    }
    _validator(schema).validate(entry)


def test_non_manual_entry_with_ss_unmatched_passes():
    """v3.7.3 F11: the exemption applies only to obtained_via=manual.
    A folder-scan or zotero-bbt-export entry CAN carry the
    semantic_scholar_unmatched field."""
    schema = _load_schema()
    entry = _base_entry() | {
        "obtained_via": "folder-scan",
        "contamination_signals": {"semantic_scholar_unmatched": True},
    }
    _validator(schema).validate(entry)


# --- #105 contamination_signals_backfilled_at -------------------------


def test_contamination_signals_backfilled_at_valid_iso8601_passes():
    """#105: scalar ISO-8601 timestamp recording when post-hoc backfill ran."""
    schema = _load_schema()
    entry = _base_entry() | {
        "contamination_signals": {
            "preprint_post_llm_inflection": False,
            "semantic_scholar_unmatched": False,
        },
        "contamination_signals_backfilled_at": "2026-05-15T10:30:00Z",
    }
    _validator(schema).validate(entry)


def test_contamination_signals_backfilled_at_absent_passes():
    """#105 backward compat: ingest-time entries (computed by
    bibliography_agent v3.7.3+) lack this field, which is valid."""
    schema = _load_schema()
    entry = _base_entry() | {
        "contamination_signals": {
            "preprint_post_llm_inflection": False,
            "semantic_scholar_unmatched": False,
        },
    }
    _validator(schema).validate(entry)


def test_contamination_signals_backfilled_at_non_string_rejected():
    """#105: field type is string (date-time format); integers / objects
    are rejected by JSON Schema validation."""
    import jsonschema

    schema = _load_schema()
    entry = _base_entry() | {"contamination_signals_backfilled_at": 1234567890}
    with pytest.raises(jsonschema.exceptions.ValidationError):
        _validator(schema).validate(entry)


# --- v3.9.0 schema additions: openalex_unmatched + crossref_unmatched ----
# Extended manual-entry not-rule (anyOf: ss / openalex / crossref).

def test_v3_9_0_openalex_unmatched_field_accepted():
    """v3.9.0 — schema accepts new openalex_unmatched optional boolean."""
    import jsonschema
    schema = _load_schema()
    entry = _base_entry() | {
        "contamination_signals": {
            "openalex_unmatched": True,
        }
    }
    _validator(schema).validate(entry)  # should not raise


def test_v3_9_0_crossref_unmatched_field_accepted():
    """v3.9.0 — schema accepts new crossref_unmatched optional boolean."""
    import jsonschema
    schema = _load_schema()
    entry = _base_entry() | {
        "contamination_signals": {
            "crossref_unmatched": False,
        }
    }
    _validator(schema).validate(entry)


def test_v3_9_0_all_four_contamination_fields_accepted():
    """v3.9.0 — schema accepts all four contamination fields together."""
    import jsonschema
    schema = _load_schema()
    entry = _base_entry() | {
        "contamination_signals": {
            "preprint_post_llm_inflection": False,
            "semantic_scholar_unmatched": True,
            "openalex_unmatched": True,
            "crossref_unmatched": True,
        },
        "year": 2024,  # preprint flag false so no year constraint
    }
    _validator(schema).validate(entry)


def test_v3_9_0_manual_entry_with_openalex_unmatched_rejected():
    """v3.9.0 — manual entry MUST NOT carry openalex_unmatched (extended not-rule)."""
    import jsonschema
    schema = _load_schema()
    entry = _base_entry() | {
        "obtained_via": "manual",
        "contamination_signals": {"openalex_unmatched": True},
    }
    with pytest.raises(jsonschema.ValidationError):
        _validator(schema).validate(entry)


def test_v3_9_0_manual_entry_with_crossref_unmatched_rejected():
    """v3.9.0 — manual entry MUST NOT carry crossref_unmatched."""
    import jsonschema
    schema = _load_schema()
    entry = _base_entry() | {
        "obtained_via": "manual",
        "contamination_signals": {"crossref_unmatched": False},
    }
    with pytest.raises(jsonschema.ValidationError):
        _validator(schema).validate(entry)


def test_v3_9_0_manual_entry_with_preprint_flag_passes():
    """v3.9.0 — manual entry MAY carry preprint_post_llm_inflection (heuristic, not lookup)."""
    import jsonschema
    schema = _load_schema()
    entry = _base_entry() | {
        "obtained_via": "manual",
        "year": 2024,
        "venue": "arXiv",
        "contamination_signals": {"preprint_post_llm_inflection": True},
    }
    _validator(schema).validate(entry)  # should not raise
