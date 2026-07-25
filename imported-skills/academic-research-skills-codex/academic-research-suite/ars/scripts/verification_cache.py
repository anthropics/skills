#!/usr/bin/env python3
"""Persistent verification cache for the bibliographic resolvers (Delta 2).

A local SQLite-backed cache so the same paper cited across multiple drafts
does not re-hit Crossref / OpenAlex / Semantic Scholar / arXiv every run.

Cache key: (citation_key, resolver_name, query_form).
  - resolver_name ∈ {crossref, openalex, semantic_scholar, arxiv}
  - query_form is the canonical-form DOI / arXiv ID / title-query string the
    resolver was keyed on (the caller passes whichever it used).
Cache value: the resolver's structured response (any JSON-serializable dict)
plus a verification_timestamp.

TTL: entries older than 90 days are treated as a miss. The 90-day window is a
guess pending empirical tuning (spec OQ-1, deferred).

Concurrency: SQLite WAL mode (single-writer-many-readers). The audit pipeline
is single-process; multi-user shared cache is out of scope (spec Delta 2).

Spec: docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md §2 Delta 2.
"""
from __future__ import annotations

import json
import os
import sqlite3
from contextlib import closing
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any

# Spec OQ-1: 90-day window is a guess, deferred for empirical tuning.
_TTL_DAYS = 90

_DEFAULT_PATH = Path.home() / ".cache" / "ars" / "verification.db"
_ENV_PATH = "ARS_VERIFICATION_CACHE_PATH"

_SCHEMA = """
CREATE TABLE IF NOT EXISTS verification_cache (
    citation_key           TEXT NOT NULL,
    resolver_name          TEXT NOT NULL,
    query_form             TEXT NOT NULL,
    response_json          TEXT NOT NULL,
    verification_timestamp TEXT NOT NULL,
    PRIMARY KEY (citation_key, resolver_name, query_form)
)
"""


def _resolve_path(path: str | None) -> Path:
    """Explicit arg wins over the env override, which wins over the default."""
    if path is not None:
        return Path(path)
    env = os.environ.get(_ENV_PATH)
    if env:
        return Path(env)
    return _DEFAULT_PATH


class VerificationCache:
    """SQLite-backed (citation_key, resolver_name, query_form) → response cache.

    Single-process use. Each method opens a short-lived connection so the
    cache holds no long-lived file handle across pipeline stages.
    """

    def __init__(self, path: str | None = None) -> None:
        self.path = str(_resolve_path(path))
        Path(self.path).parent.mkdir(parents=True, exist_ok=True)
        # `closing(...) as conn, conn` — the outer ctx closes the handle, the
        # inner (the connection itself) commits/rolls back. Honors the
        # short-lived-connection contract (no leaked handle across stages).
        with closing(self._connect()) as conn, conn:
            conn.execute(_SCHEMA)

    def _connect(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.path)
        # WAL: single-writer-many-readers safety (spec Delta 2). Persistent
        # journal-mode pragma — set on every connection (cheap; no-op when
        # already WAL).
        conn.execute("PRAGMA journal_mode=WAL")
        return conn

    def get(
        self, citation_key: str, resolver_name: str, query_form: str,
    ) -> dict[str, Any] | None:
        """Return the cached response, or None on miss / expired entry.

        An entry whose verification_timestamp is older than the TTL is a
        miss (the caller then makes the live call and re-populates).
        """
        with closing(self._connect()) as conn:
            row = conn.execute(
                "SELECT response_json, verification_timestamp "
                "FROM verification_cache "
                "WHERE citation_key = ? AND resolver_name = ? AND query_form = ?",
                (citation_key, resolver_name, query_form),
            ).fetchone()
        if row is None:
            return None
        response_json, ts = row
        if self._is_expired(ts):
            return None
        # #331: a corrupted payload (not decodable) or a non-dict value (e.g.
        # written by an older/other tool) is a miss, not a hard error — the
        # documented contract is "malformed cache payload = miss". Returning None
        # forces a clean live recompute instead of aborting verification with a
        # JSONDecodeError or handing the caller a shape it cannot read.
        try:
            value = json.loads(response_json)
        except (json.JSONDecodeError, TypeError):
            return None
        if not isinstance(value, dict):
            return None
        return value

    def put(
        self,
        citation_key: str,
        resolver_name: str,
        query_form: str,
        response: dict[str, Any],
    ) -> None:
        """Store (or overwrite) the resolver response, stamping it now (UTC)."""
        now = datetime.now(timezone.utc).isoformat()
        with closing(self._connect()) as conn, conn:
            conn.execute(
                "INSERT OR REPLACE INTO verification_cache "
                "(citation_key, resolver_name, query_form, response_json, "
                " verification_timestamp) VALUES (?, ?, ?, ?, ?)",
                (
                    citation_key,
                    resolver_name,
                    query_form,
                    json.dumps(response),
                    now,
                ),
            )

    def invalidate(self, citation_key: str) -> None:
        """Drop every cached entry (all resolvers, all query forms) for a
        citation. Backs the /ars-cache-invalidate command. No-op when the
        citation has no cached rows."""
        with closing(self._connect()) as conn, conn:
            conn.execute(
                "DELETE FROM verification_cache WHERE citation_key = ?",
                (citation_key,),
            )

    @staticmethod
    def _is_expired(verification_timestamp: str) -> bool:
        stored = datetime.fromisoformat(verification_timestamp)
        return datetime.now(timezone.utc) - stored > timedelta(days=_TTL_DAYS)
