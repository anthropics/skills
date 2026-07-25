#!/usr/bin/env python3
"""Canonical repro_lock field set — single source of truth (#260).

The `repro_lock` block is declared in two places:
  1. The standalone passport-level validator (`scripts/check_repro_lock.py`).
  2. The nested `repro_lock` sub-shape inside
     `shared/contracts/passport/experiment_provenance_entry.schema.json`
     (each experiment_provenance[] entry carries its own lock, #260 D1).

Without a single source, the two copies silently diverge over time. This
module holds the canonical required-field constants; both `check_repro_lock.py`
imports them, and a drift test
(`scripts/test_repro_lock_validation_drift.py`) asserts the nested schema's
required keys equal these constants. See
shared/artifact_reproducibility_pattern.md for the field-by-field rationale.

This module is pure data + a stateless validate function — no I/O, no CLI.
"""
from __future__ import annotations

from typing import Any

SUPPORTED_SCHEMA_VERSIONS = {"1.0"}
SUPPORTED_HASH_TIMINGS = {"skill-load"}

REQUIRED_FIELDS = {
    "schema_version",
    "stochasticity_declaration",
    "ars_version",
    "model",
    "prompts",
    "materials",
    "external_protocols",
    "cross_model",
}

REQUIRED_MODEL = {"family", "id", "weight_stable"}
REQUIRED_PROMPTS = {"hash_timing", "skill_md_hash", "agents_bundle_hash"}
REQUIRED_MATERIALS = {"list_hash", "count"}
REQUIRED_EXTERNAL = {"s2_api_protocol_version", "s2_snapshot_available"}
REQUIRED_CROSSMODEL = {"enabled", "secondary_model_id"}

# (sub-block name, required field set) pairs, iteration-ordered for stable output.
_SUBBLOCKS = (
    ("model", REQUIRED_MODEL),
    ("prompts", REQUIRED_PROMPTS),
    ("materials", REQUIRED_MATERIALS),
    ("external_protocols", REQUIRED_EXTERNAL),
    ("cross_model", REQUIRED_CROSSMODEL),
)


def validate_block(lock: dict[str, Any]) -> list[str]:
    """Validate a populated repro_lock mapping; return a list of error strings.

    Shape-only: caller handles the missing-key / null-opt-out / non-mapping
    top-level cases (those need passport-level context the block alone lacks).
    """
    errors: list[str] = []

    missing = REQUIRED_FIELDS - set(lock.keys())
    for m in sorted(missing):
        errors.append(f"repro_lock: missing required field '{m}'")

    sv = lock.get("schema_version")
    if sv is not None and sv not in SUPPORTED_SCHEMA_VERSIONS:
        errors.append(
            f"repro_lock.schema_version = {sv!r}, must be one of {sorted(SUPPORTED_SCHEMA_VERSIONS)}"
        )

    for name, required in _SUBBLOCKS:
        sub = lock.get(name)
        if sub is None:
            continue  # missing top-level already reported
        if not isinstance(sub, dict):
            errors.append(f"repro_lock.{name} must be a mapping")
            continue
        for m in sorted(required - set(sub.keys())):
            errors.append(f"repro_lock.{name}: missing required field '{m}'")

    prompts = lock.get("prompts")
    if isinstance(prompts, dict):
        ht = prompts.get("hash_timing")
        if ht is not None and ht not in SUPPORTED_HASH_TIMINGS:
            errors.append(
                f"repro_lock.prompts.hash_timing = {ht!r}, "
                f"must be one of {sorted(SUPPORTED_HASH_TIMINGS)} (see shared/artifact_reproducibility_pattern.md)"
            )

    return errors
