"""Shared helpers for ARS reference adapters.

These helpers are used by folder_scan.py, zotero.py, and obsidian.py.
They are also what a user-written adapter would copy and adapt.
"""
from __future__ import annotations
import datetime
import io
import re
from pathlib import Path
from typing import Any

import yaml


def path_to_file_uri(path: Path | str) -> str:
    """Build an RFC 8089 ``file://`` URI from a filesystem path.

    Uses ``Path.as_uri()`` after resolving so spaces and reserved
    characters are percent-encoded (``Lee 2024 paper.pdf`` →
    ``file:///.../Lee%202024%20paper.pdf``). Naive ``f"file://{path}"``
    yields invalid URIs and is the codex-flagged P1 from T7.
    """
    return Path(path).resolve().as_uri()

ADAPTER_SPEC_VERSION = "1.0.0"  # bump when overview.md contract changes

_NON_ALNUM = re.compile(r"[^A-Za-z0-9]+")
_TITLE_WORD = re.compile(r"[A-Za-z]+")
_STOPWORDS = {
    "a", "an", "the", "of", "in", "on", "at", "by", "for", "to", "with",
    "and", "or", "but", "is", "are", "was", "were",
}


def sanitize_citation_key(raw: str) -> str:
    """Strip non-alphanumeric characters. Does NOT lowercase."""
    return _NON_ALNUM.sub("", raw)


def _first_title_word_non_stopword(title_hint: str | None) -> str:
    if not title_hint:
        return ""
    for word in _TITLE_WORD.findall(title_hint):
        if word.lower() not in _STOPWORDS:
            return word.lower()
    return ""


def _alpha_suffixes():
    """Yield 'a', 'b', ..., 'z', 'aa', 'ab', ..., 'zz'."""
    for c in "abcdefghijklmnopqrstuvwxyz":
        yield c
    for c1 in "abcdefghijklmnopqrstuvwxyz":
        for c2 in "abcdefghijklmnopqrstuvwxyz":
            yield c1 + c2


def make_citation_key(
    *, family: str, year: int, title_hint: str | None, existing: set[str]
) -> str:
    """Build a collision-safe citation key.

    Pattern: {family_lower}{year}{first_title_word_or_empty}. If that is
    already in `existing`, append `a`, `b`, `c`, ... (then aa, ab, ...).
    The chosen key is added to `existing` by reference.

    Falls back to "ref" when the sanitized base is empty (e.g., empty
    family with year=0 and no title_hint).
    """
    base = f"{family.lower()}{year}{_first_title_word_non_stopword(title_hint)}"
    base = sanitize_citation_key(base)
    # citation_key schema requires ^[A-Za-z]... so a pure-digit base
    # (e.g. family='' year=2024) would fail schema validation. Fall back.
    if not base or not base[0].isalpha():
        base = "ref"

    if base not in existing:
        existing.add(base)
        return base

    for suffix in _alpha_suffixes():
        candidate = f"{base}{suffix}"
        if candidate not in existing:
            existing.add(candidate)
            return candidate
    raise RuntimeError("exhausted citation key suffix space")  # practically unreachable


def ensure_unique_citekey(key: str, existing: set[str]) -> str:
    """Disambiguate a pre-existing citation key against ``existing``.

    Used by adapters whose source already supplies a citekey (zotero
    Better BibTeX, obsidian frontmatter ``citekey:``). The returned
    key is sanitized to satisfy the schema pattern
    ``^[A-Za-z][A-Za-z0-9_:-]*$`` and is added to ``existing`` by
    reference. Collisions get an alpha suffix (a, b, ..., z, aa, ...)
    just like ``make_citation_key``.

    Empty / leading-digit / leading-punct bases fall back to ``ref``.
    """
    cleaned_chars = []
    for ch in key:
        if ch.isalnum() or ch in "_:-":
            cleaned_chars.append(ch)
    base = "".join(cleaned_chars)
    if not base or not base[0].isalpha():
        # Prefix with 'ref' so the result satisfies the schema's
        # leading-letter constraint while preserving the original
        # numeric/punctuated tail when one exists.
        base = f"ref{base}" if base else "ref"

    if base not in existing:
        existing.add(base)
        return base

    for suffix in _alpha_suffixes():
        candidate = f"{base}{suffix}"
        if candidate not in existing:
            existing.add(candidate)
            return candidate
    raise RuntimeError("exhausted citation key suffix space")


def parse_csl_name(raw: str) -> dict[str, str]:
    """Parse a single name string into a CSL-JSON name object.

    Rules:
    - "{Institution Name}" -> {"literal": "Institution Name"}
    - "Family, Given" -> {"family": "Family", "given": "Given"}
    - "Family" (single token) -> {"family": "Family"}
    """
    raw = raw.strip()
    if raw.startswith("{") and raw.endswith("}"):
        return {"literal": raw[1:-1].strip()}
    if "," in raw:
        family, _, given = raw.partition(",")
        return {"family": family.strip(), "given": given.strip()}
    return {"family": raw}


def parse_semicolon_names(raw: str) -> list[dict[str, str]]:
    """Parse 'A, B; C, D' into a CSL name list. Empty segments are skipped."""
    raw = raw.strip()
    if not raw:
        return []
    return [parse_csl_name(part) for part in raw.split(";") if part.strip()]


def dump_yaml_stable(data: Any) -> str:
    """Dump YAML with sorted keys and deterministic formatting."""
    buf = io.StringIO()
    yaml.safe_dump(
        data,
        buf,
        sort_keys=True,
        default_flow_style=False,
        allow_unicode=True,
        width=1000,
    )
    return buf.getvalue()


def now_iso() -> str:
    """ISO 8601 in UTC with trailing 'Z' (RFC 3339 compatible)."""
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def write_passport(path: Path, entries: list[dict[str, Any]]) -> None:
    """Write passport.yaml with literature_corpus[] sorted by citation_key."""
    sorted_entries = sorted(entries, key=lambda e: e.get("citation_key", ""))
    doc = {"literature_corpus": sorted_entries}
    path.write_text(dump_yaml_stable(doc), encoding="utf-8")


def write_rejection_log(
    path: Path,
    *,
    adapter_name: str,
    adapter_version: str,
    rejected: list[dict[str, Any]],
    input_source: str | None = None,
    total_input: int | None = None,
    total_accepted: int | None = None,
) -> None:
    """Write rejection_log.yaml with rejected[] sorted by source.

    summary.total_rejected is always set from len(rejected). When the caller
    knows the upstream input or accept count, pass total_input / total_accepted
    so the summary tells the full story; otherwise those keys are omitted.
    """
    sorted_rejected = sorted(rejected, key=lambda r: r.get("source", ""))
    summary: dict[str, int] = {"total_rejected": len(sorted_rejected)}
    if total_input is not None:
        summary["total_input"] = total_input
    if total_accepted is not None:
        summary["total_accepted"] = total_accepted

    doc: dict[str, Any] = {
        "adapter_name": adapter_name,
        "adapter_version": adapter_version,
        "generated_at": now_iso(),
        "rejected": sorted_rejected,
        "summary": summary,
    }
    if input_source is not None:
        doc["input_source"] = input_source

    path.write_text(dump_yaml_stable(doc), encoding="utf-8")
