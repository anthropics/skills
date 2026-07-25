"""Validates rejection_log.schema.json self-consistency and example round-trip."""
from pathlib import Path
import json
import pytest
from jsonschema import Draft202012Validator
from jsonschema.exceptions import ValidationError

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "shared/contracts/passport/rejection_log.schema.json"


def _load_schema():
    with SCHEMA_PATH.open("r", encoding="utf-8") as f:
        return json.load(f)


def _validator(schema):
    """Validator with format_checker so format keywords (date-time on
    generated_at) are actually enforced. Same pattern as T2's
    test_literature_corpus_entry_schema._validator."""
    return Draft202012Validator(
        schema, format_checker=Draft202012Validator.FORMAT_CHECKER
    )


def test_schema_exists():
    assert SCHEMA_PATH.exists()


def test_schema_self_consistent():
    schema = _load_schema()
    Draft202012Validator.check_schema(schema)


def test_empty_rejected_is_valid():
    schema = _load_schema()
    log = {
        "adapter_name": "zotero.py",
        "adapter_version": "1.0.0",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [],
    }
    _validator(schema).validate(log)


def test_missing_required_top_level_fails():
    schema = _load_schema()
    log = {"adapter_name": "x", "adapter_version": "1", "rejected": []}
    with pytest.raises(ValidationError):
        _validator(schema).validate(log)


def test_rejection_with_object_raw():
    schema = _load_schema()
    log = {
        "adapter_name": "zotero.py",
        "adapter_version": "1.0.0",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [
            {
                "source": "0_ABCD1234",
                "reason": "missing_required_field",
                "missing_fields": ["authors"],
                "raw": {"title": "Foo", "date": "n.d."},
            }
        ],
    }
    _validator(schema).validate(log)


def test_rejection_with_string_raw():
    schema = _load_schema()
    log = {
        "adapter_name": "folder_scan.py",
        "adapter_version": "1.0.0",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [
            {
                "source": "paper1.pdf",
                "reason": "authors_unparseable",
                "raw": "paper1.pdf",
            }
        ],
    }
    _validator(schema).validate(log)


def test_rejection_with_array_raw_rejected():
    schema = _load_schema()
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [
            {
                "source": "s",
                "reason": "other",
                "detail": "d",
                "raw": ["not", "allowed"],
            }
        ],
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(log)


def test_reason_enum_constrained():
    schema = _load_schema()
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [{"source": "s", "reason": "invented_reason"}],
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(log)


def test_additional_properties_false_on_rejection():
    schema = _load_schema()
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [
            {"source": "s", "reason": "other", "detail": "d", "bogus": 1}
        ],
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(log)


# --- conditional enforcement: detail required when reason='other' ---
# Spec §4 says "Required when reason='other'. Recommended otherwise."
# Following the T2 lesson (codex review caught the same prose-only
# conditional pattern for adapter_name), we enforce this via allOf
# at schema-write time and test it here.

def test_reason_other_without_detail_fails():
    schema = _load_schema()
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [{"source": "s", "reason": "other"}],
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(log)


def test_reason_other_with_detail_passes():
    schema = _load_schema()
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [
            {"source": "s", "reason": "other", "detail": "explained why"}
        ],
    }
    _validator(schema).validate(log)


def test_reason_known_value_does_not_require_detail():
    """Conditional only fires for reason='other'. Categorical reasons
    (missing_required_field, etc.) must validate without detail."""
    schema = _load_schema()
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [{"source": "s", "reason": "missing_required_field"}],
    }
    _validator(schema).validate(log)


# --- format enforcement (T2 lesson) ---

def test_invalid_generated_at_format_fails():
    schema = _load_schema()
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "not-a-date",
        "rejected": [],
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(log)


# --- T3-review P2 + test gaps (codex 2026-04-25) ---

def test_reason_other_with_empty_detail_fails():
    """detail must be non-empty when present. Spec calls it a
    'free-text explanation'; empty string defeats that contract.
    Schema enforces via detail.minLength=1."""
    schema = _load_schema()
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [{"source": "s", "reason": "other", "detail": ""}],
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(log)


def test_top_level_additional_properties_rejected():
    schema = _load_schema()
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [],
        "bogus_top_level": "nope",
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(log)


def test_input_source_round_trip():
    schema = _load_schema()
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "2026-04-23T00:00:00Z",
        "input_source": "/path/to/refs",
        "rejected": [],
    }
    _validator(schema).validate(log)


def test_summary_round_trip():
    schema = _load_schema()
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [],
        "summary": {
            "total_input": 10,
            "total_accepted": 7,
            "total_rejected": 3,
        },
    }
    _validator(schema).validate(log)


def test_summary_rejects_unknown_field():
    schema = _load_schema()
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [],
        "summary": {"total_input": 1, "made_up": 0},
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(log)


def test_rejection_missing_source_fails():
    schema = _load_schema()
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [{"reason": "adapter_error"}],
    }
    with pytest.raises(ValidationError):
        _validator(schema).validate(log)
