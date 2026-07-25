#!/usr/bin/env python3
"""Tests for the persistent verification cache (Delta 2).

Spec: docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md §2 Delta 2.

The cache is a local SQLite-backed store keyed by
(citation_key, resolver_name, query_form). All tests point
ARS_VERIFICATION_CACHE_PATH at a tmp file so no real ~/.cache/ars/ db is
touched and runs are isolated.
"""
from __future__ import annotations

import sqlite3
from datetime import datetime, timedelta, timezone

import pytest


@pytest.fixture()
def cache(tmp_path, monkeypatch):
    from verification_cache import VerificationCache

    db = tmp_path / "verification.db"
    monkeypatch.setenv("ARS_VERIFICATION_CACHE_PATH", str(db))
    return VerificationCache()


def test_put_then_get_round_trip(cache):
    cache.put("smith2024", "crossref", "10.5555/abc", {"matched": True})
    got = cache.get("smith2024", "crossref", "10.5555/abc")
    assert got is not None
    assert got["matched"] is True


def test_miss_returns_none(cache):
    assert cache.get("nobody2024", "crossref", "10.5555/none") is None


def test_distinct_resolvers_same_citation_are_independent(cache):
    cache.put("smith2024", "crossref", "10.5555/abc", {"src": "cr"})
    cache.put("smith2024", "arxiv", "1706.03762", {"src": "ax"})
    assert cache.get("smith2024", "crossref", "10.5555/abc")["src"] == "cr"
    assert cache.get("smith2024", "arxiv", "1706.03762")["src"] == "ax"


def test_distinct_query_form_same_resolver_independent(cache):
    cache.put("smith2024", "crossref", "10.5555/abc", {"via": "doi"})
    cache.put("smith2024", "crossref", "smith attention 2024", {"via": "title"})
    assert cache.get("smith2024", "crossref", "10.5555/abc")["via"] == "doi"
    assert cache.get(
        "smith2024", "crossref", "smith attention 2024"
    )["via"] == "title"


def test_put_overwrites_same_key(cache):
    cache.put("smith2024", "crossref", "10.5555/abc", {"matched": False})
    cache.put("smith2024", "crossref", "10.5555/abc", {"matched": True})
    assert cache.get("smith2024", "crossref", "10.5555/abc")["matched"] is True


def test_expired_entry_returns_none(tmp_path, monkeypatch):
    """An entry older than the TTL (90 days) is a miss."""
    from verification_cache import VerificationCache, _TTL_DAYS

    db = tmp_path / "verification.db"
    monkeypatch.setenv("ARS_VERIFICATION_CACHE_PATH", str(db))
    c = VerificationCache()
    c.put("old2020", "crossref", "10.5555/old", {"matched": True})

    # Backdate the stored verification_timestamp past the TTL by writing
    # directly to the underlying row.
    stale = (
        datetime.now(timezone.utc) - timedelta(days=_TTL_DAYS + 1)
    ).isoformat()
    conn = sqlite3.connect(str(db))
    conn.execute(
        "UPDATE verification_cache SET verification_timestamp = ? "
        "WHERE citation_key = ?",
        (stale, "old2020"),
    )
    conn.commit()
    conn.close()

    assert c.get("old2020", "crossref", "10.5555/old") is None


def test_fresh_entry_within_ttl_returns_value(tmp_path, monkeypatch):
    from verification_cache import VerificationCache, _TTL_DAYS

    db = tmp_path / "verification.db"
    monkeypatch.setenv("ARS_VERIFICATION_CACHE_PATH", str(db))
    c = VerificationCache()
    c.put("recent2026", "arxiv", "2605.18661", {"matched": True})

    fresh = (
        datetime.now(timezone.utc) - timedelta(days=_TTL_DAYS - 1)
    ).isoformat()
    conn = sqlite3.connect(str(db))
    conn.execute(
        "UPDATE verification_cache SET verification_timestamp = ? "
        "WHERE citation_key = ?",
        (fresh, "recent2026"),
    )
    conn.commit()
    conn.close()

    got = c.get("recent2026", "arxiv", "2605.18661")
    assert got is not None and got["matched"] is True


def test_invalidate_removes_all_resolvers_for_citation(cache):
    cache.put("smith2024", "crossref", "10.5555/abc", {"src": "cr"})
    cache.put("smith2024", "arxiv", "1706.03762", {"src": "ax"})
    cache.put("jones2024", "crossref", "10.5555/xyz", {"src": "cr2"})

    cache.invalidate("smith2024")

    assert cache.get("smith2024", "crossref", "10.5555/abc") is None
    assert cache.get("smith2024", "arxiv", "1706.03762") is None
    # Other citations untouched.
    assert cache.get("jones2024", "crossref", "10.5555/xyz")["src"] == "cr2"


def test_invalidate_unknown_citation_is_noop(cache):
    # Should not raise.
    cache.invalidate("never-stored")


def test_env_path_override_is_honored(tmp_path, monkeypatch):
    from verification_cache import VerificationCache

    db = tmp_path / "custom" / "mycache.db"
    monkeypatch.setenv("ARS_VERIFICATION_CACHE_PATH", str(db))
    c = VerificationCache()
    c.put("k", "crossref", "q", {"v": 1})
    assert db.exists(), "cache file must be created at the env-override path"


def test_explicit_path_arg_overrides_env(tmp_path, monkeypatch):
    from verification_cache import VerificationCache

    env_db = tmp_path / "env.db"
    arg_db = tmp_path / "arg.db"
    monkeypatch.setenv("ARS_VERIFICATION_CACHE_PATH", str(env_db))
    c = VerificationCache(path=str(arg_db))
    c.put("k", "crossref", "q", {"v": 1})
    assert arg_db.exists()
    assert not env_db.exists(), "explicit path arg must win over env var"


def test_wal_mode_enabled(cache):
    """SQLite WAL mode for single-writer-many-readers safety (spec Delta 2)."""
    conn = sqlite3.connect(cache.path)
    mode = conn.execute("PRAGMA journal_mode").fetchone()[0]
    conn.close()
    assert mode.lower() == "wal"


def test_response_roundtrips_nested_structure(cache):
    """Resolver responses are arbitrary JSON-serializable dicts."""
    payload = {
        "matched": True,
        "resolver_outcomes": {"crossref": {"status": "matched"}},
        "title": "Attention Is All You Need",
        "year": 2017,
    }
    cache.put("vaswani2017", "crossref", "10.5555/abc", payload)
    assert cache.get("vaswani2017", "crossref", "10.5555/abc") == payload


def test_corrupted_json_payload_is_miss(tmp_path, monkeypatch):
    """#331 P3: a row whose response_json is not decodable JSON is a miss
    (return None → live recompute), not a JSONDecodeError that aborts
    verification. Contract: 'malformed cache payload = miss'."""
    from verification_cache import VerificationCache

    db = tmp_path / "verification.db"
    monkeypatch.setenv("ARS_VERIFICATION_CACHE_PATH", str(db))
    c = VerificationCache()
    c.put("bad2024", "crossref", "10.5555/bad", {"matched": True})

    conn = sqlite3.connect(str(db))
    conn.execute(
        "UPDATE verification_cache SET response_json = ? WHERE citation_key = ?",
        ("{not valid json", "bad2024"),
    )
    conn.commit()
    conn.close()

    assert c.get("bad2024", "crossref", "10.5555/bad") is None


def test_non_dict_payload_is_miss(tmp_path, monkeypatch):
    """#331 P3: a row decoding to a non-dict value (e.g. a bare list/string from
    an older or manual writer) is a miss — the caller's `"matched" in cached`
    join logic expects a dict. Return None rather than hand back a shape the
    caller cannot read."""
    from verification_cache import VerificationCache

    db = tmp_path / "verification.db"
    monkeypatch.setenv("ARS_VERIFICATION_CACHE_PATH", str(db))
    c = VerificationCache()
    c.put("list2024", "crossref", "10.5555/list", {"matched": True})

    conn = sqlite3.connect(str(db))
    conn.execute(
        "UPDATE verification_cache SET response_json = ? WHERE citation_key = ?",
        ('["matched", true]', "list2024"),  # valid JSON, but a list not a dict
    )
    conn.commit()
    conn.close()

    assert c.get("list2024", "crossref", "10.5555/list") is None
