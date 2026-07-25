#!/usr/bin/env python3
"""Tests for the /ars-cache-invalidate CLI shim (Delta 2, deliverable 6).

Spec: docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md §2 Delta 2.
"""
from __future__ import annotations

import pytest


@pytest.fixture()
def seeded_cache(tmp_path, monkeypatch):
    """A VerificationCache with two citations cached across resolvers."""
    from verification_cache import VerificationCache

    db = tmp_path / "verification.db"
    monkeypatch.setenv("ARS_VERIFICATION_CACHE_PATH", str(db))
    c = VerificationCache()
    c.put("smith2024", "crossref", "doi:10.5/x|title:T", {"matched": True})
    c.put("smith2024", "arxiv", "arxiv:1.2|title:T", {"matched": False})
    c.put("jones2024", "crossref", "doi:10.5/y|title:U", {"matched": True})
    return c, db


def test_invalidate_removes_named_citation(seeded_cache, monkeypatch):
    from ars_cache_invalidate import main
    from verification_cache import VerificationCache

    cache, db = seeded_cache
    rc = main(["smith2024"])
    assert rc == 0

    fresh = VerificationCache()  # reads same env path
    assert fresh.get("smith2024", "crossref", "doi:10.5/x|title:T") is None
    assert fresh.get("smith2024", "arxiv", "arxiv:1.2|title:T") is None
    # Other citation untouched.
    assert fresh.get("jones2024", "crossref", "doi:10.5/y|title:U") is not None


def test_invalidate_unknown_citation_is_noop_success(seeded_cache):
    from ars_cache_invalidate import main

    rc = main(["never-cached"])
    assert rc == 0  # idempotent no-op, not an error


def test_missing_argument_is_usage_error(seeded_cache):
    from ars_cache_invalidate import main

    with pytest.raises(SystemExit):  # argparse exits on missing required arg
        main([])
