#!/usr/bin/env python3
"""obsidian: produce a literature_corpus passport from an Obsidian vault.

Convention A (preferred): frontmatter carries citekey/title/authors/year/...
Convention B (Karpathy-style): filename is the citekey, body has an H1 title
and a "**Authors**: A, B.; C, D." line, year from **Year**: line or frontmatter
source URL.

Files under _templates/ and .obsidian/ are skipped. Files that match neither
convention are rejected.

Usage:
  python scripts/adapters/obsidian.py \\
      --input <vault_dir> --passport <out.yaml> --rejection-log <out.yaml>
"""
from __future__ import annotations
import argparse
import re
import sys
import urllib.parse
from pathlib import Path
from typing import Any

import yaml

# Allow running as a script: ensure repo root is importable for
# `from scripts.adapters._common import ...`
_THIS = Path(__file__).resolve()
_REPO_ROOT = _THIS.parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from scripts.adapters._common import (  # noqa: E402
    write_passport,
    write_rejection_log,
    parse_semicolon_names,
    ensure_unique_citekey,
    now_iso,
)

ADAPTER_NAME = "obsidian.py"
ADAPTER_VERSION = "1.1.0"

SKIP_DIR_NAMES = {"_templates", ".obsidian"}

# v3.10 (spec §3 PR-B item 13): valid venue_type enum values an obsidian note's
# frontmatter may declare. A markdown vault carries no structured source-type
# metadata, so the default is unknown/unknown; an explicit `venue_type` frontmatter
# field (a deliberate user declaration) is honored as `user_declared` IFF it is a
# valid enum member. Never inferred from free-form text (R-L3-2-D).
VALID_VENUE_TYPES = frozenset({
    "journal-article", "conference-paper", "book", "chapter", "dissertation",
    "preprint", "report", "dataset", "other", "unknown",
})


def declare_venue_type(fm: Any) -> tuple[str, str]:
    """Return (venue_type, venue_type_provenance) for an obsidian note.

    A frontmatter `venue_type` that is a valid enum member is honored as
    user_declared (with the unknown⟹unknown invariant enforced). Anything else —
    absent, invalid, or `unknown` — yields unknown/unknown. Honors the pair
    invariant: the two are always emitted together."""
    declared = fm.get("venue_type") if isinstance(fm, dict) else None
    if isinstance(declared, str) and declared in VALID_VENUE_TYPES and declared != "unknown":
        return declared, "user_declared"
    return "unknown", "unknown"

RE_FRONTMATTER = re.compile(r"^---\n(.*?)\n---\n(.*)$", re.DOTALL)
RE_H1 = re.compile(r"^#\s+(.+)$", re.MULTILINE)
RE_AUTHORS_LINE = re.compile(r"^\*\*Authors\*\*:\s*(.+)$", re.MULTILINE)
RE_YEAR_LINE = re.compile(r"^\*\*Year\*\*:\s*((?:19|20)\d{2})\s*$", re.MULTILINE)
RE_YEAR_IN_SOURCE = re.compile(r"((?:19|20)\d{2})")


# Sentinel: split_frontmatter uses this when '---' is present but YAML is invalid,
# so callers can reject malformed files rather than silently falling through to
# Convention B (which would misclassify the filename stem as a valid citekey).
_SENTINEL_MALFORMED = object()


def split_frontmatter(content: str) -> tuple[Any, str]:
    """Parse YAML frontmatter from `content`.

    Returns (fm, body) where:
    - fm is a dict            → valid frontmatter
    - fm is None              → no leading '---' delimiter (fall through to Convention B)
    - fm is _SENTINEL_MALFORMED → '---' present but YAML invalid (reject as malformed)
    """
    m = RE_FRONTMATTER.match(content)
    if not m:
        return None, content
    try:
        fm = yaml.safe_load(m.group(1)) or {}
    except yaml.YAMLError as exc:
        return _SENTINEL_MALFORMED, str(exc)
    if not isinstance(fm, dict):
        return _SENTINEL_MALFORMED, f"frontmatter parsed as {type(fm).__name__}, expected mapping"
    return fm, m.group(2)


def build_pointer(vault_name: str, rel_path: Path) -> str:
    """Build an obsidian:// URI for a vault file.

    Uses URL percent-encoding for vault name and relative path (without
    extension), matching the Obsidian URI scheme
    obsidian://open?vault=NAME&file=RELATIVE_PATH.
    """
    return (
        "obsidian://open?"
        f"vault={urllib.parse.quote(vault_name)}"
        f"&file={urllib.parse.quote(str(rel_path.with_suffix('')))}"
    )


def _coerce_year(raw: Any) -> tuple[int | None, str | None]:
    """Try to parse year to int.

    Returns (year_int, None) on success, or (None, error_detail) on failure.
    Accepts int directly, or a string whose first 4 characters parse as a
    4-digit year (e.g. "2024", "2024-01", "2024-01-15" all yield 2024).
    """
    if isinstance(raw, int):
        return raw, None
    if isinstance(raw, str):
        # Accept leading-year patterns: "2024", "2024-01", "2024-01-15" → 2024
        candidate = raw.strip()[:4]
        if len(candidate) == 4 and candidate.isdigit():
            return int(candidate), None
    return None, f"cannot parse year from {raw!r}"


def _coerce_authors(raw: Any) -> tuple[list[dict] | None, str | None]:
    """Coerce frontmatter authors value to a CSL name list.

    Accepts:
    - list of dicts, each with 'family' or 'literal'  → validated, returned as-is
    - str                                               → parsed via parse_semicolon_names
    Returns (authors_list, None) on success, or (None, error_detail) on failure.
    """
    if isinstance(raw, str):
        parsed = parse_semicolon_names(raw)
        if not parsed:
            return None, f"string {raw!r} yielded no parseable names"
        return parsed, None
    if isinstance(raw, list):
        for item in raw:
            if not isinstance(item, dict):
                return None, f"authors list contains non-dict item: {item!r}"
            if "family" not in item and "literal" not in item:
                return None, f"author dict missing 'family' and 'literal': {item!r}"
        return raw, None
    return None, f"authors must be a string or list, got {type(raw).__name__}"


def process_file(
    md_path: Path, vault_root: Path, vault_name: str, existing: set[str]
) -> tuple[dict | None, dict | None]:
    """Return (accepted_entry, rejection) — exactly one is None.

    `existing` is a set of already-chosen citation_key values; it is
    updated in-place when a new key is allocated.
    """
    rel = md_path.relative_to(vault_root)
    raw = md_path.read_text(encoding="utf-8")
    fm, body = split_frontmatter(raw)

    if fm is _SENTINEL_MALFORMED:
        return None, {
            "source": str(rel),
            "reason": "invalid_field_format",
            "detail": f"YAML frontmatter parse error: {body}",
            "raw": str(rel),
        }

    # Convention A: frontmatter has citekey
    if fm is not None and "citekey" in fm:
        missing = [k for k in ("citekey", "title", "authors", "year") if not fm.get(k)]
        if missing:
            return None, {
                "source": str(rel),
                "reason": "missing_required_field",
                "missing_fields": missing,
                "raw": str(rel),
            }

        year_val, year_err = _coerce_year(fm["year"])
        if year_err is not None:
            return None, {
                "source": str(rel),
                "reason": "year_unparseable",
                "detail": year_err,
                "raw": str(rel),
            }

        authors_val, authors_err = _coerce_authors(fm["authors"])
        if authors_err is not None:
            return None, {
                "source": str(rel),
                "reason": "authors_unparseable",
                "detail": authors_err,
                "raw": str(rel),
            }

        citation_key = ensure_unique_citekey(str(fm["citekey"]), existing)

        entry: dict[str, Any] = {
            "citation_key": citation_key,
            "title": str(fm["title"]),
            "authors": authors_val,
            "year": year_val,
            "source_pointer": build_pointer(vault_name, rel),
            "obtained_via": "obsidian-vault",
            "obtained_at": now_iso(),
            "adapter_name": ADAPTER_NAME,
            "adapter_version": ADAPTER_VERSION,
        }
        for opt in ("venue", "doi", "tags"):
            if fm.get(opt):
                entry[opt] = fm[opt]
        vt, vtp = declare_venue_type(fm)
        entry["venue_type"] = vt
        entry["venue_type_provenance"] = vtp
        body_stripped = body.strip()
        if body_stripped:
            entry["user_notes"] = body_stripped + "\n"
        return entry, None

    # Convention B: derive from filename + body H1 + "**Authors**:" line
    citekey = md_path.stem
    title_match = RE_H1.search(body) if body else None
    authors_line = RE_AUTHORS_LINE.search(body) if body else None
    year_match = RE_YEAR_LINE.search(body) if body else None

    title = title_match.group(1).strip() if title_match else None
    authors = parse_semicolon_names(authors_line.group(1).strip()) if authors_line else None
    year: int | None = None
    if year_match:
        year = int(year_match.group(1))
    elif fm is not None and fm.get("source"):
        ys = RE_YEAR_IN_SOURCE.search(str(fm["source"]))
        if ys:
            year = int(ys.group(1))

    missing_b: list[str] = []
    if not title:
        missing_b.append("title")
    if not authors:
        missing_b.append("authors")
    if not year:
        missing_b.append("year")

    if missing_b:
        return None, {
            "source": str(rel),
            "reason": "authors_unparseable" if "authors" in missing_b else "missing_required_field",
            "missing_fields": missing_b,
            "raw": str(rel),
        }

    citation_key = ensure_unique_citekey(citekey, existing)

    entry = {
        "citation_key": citation_key,
        "title": title,
        "authors": authors,
        "year": year,
        "source_pointer": build_pointer(vault_name, rel),
        "obtained_via": "obsidian-vault",
        "obtained_at": now_iso(),
        "adapter_name": ADAPTER_NAME,
        "adapter_version": ADAPTER_VERSION,
    }
    # Convention B has no structured frontmatter type; honor a frontmatter
    # venue_type if one is present (fm may exist even in Convention B), else
    # unknown/unknown.
    vt, vtp = declare_venue_type(fm)
    entry["venue_type"] = vt
    entry["venue_type_provenance"] = vtp
    # Strip the Authors / Year lines and H1 from user_notes
    body_clean = RE_AUTHORS_LINE.sub("", body) if body else ""
    body_clean = RE_YEAR_LINE.sub("", body_clean)
    body_clean = RE_H1.sub("", body_clean, count=1)
    body_clean = body_clean.strip()
    if body_clean:
        entry["user_notes"] = body_clean + "\n"
    return entry, None


def iter_markdown_files(vault: Path):
    """Yield .md files under vault, skipping SKIP_DIR_NAMES and hidden dirs."""
    for md in sorted(vault.rglob("*.md")):
        # Skip files whose relative path includes a skip dir or hidden dir
        parts = md.relative_to(vault).parts[:-1]
        if any(p in SKIP_DIR_NAMES or p.startswith(".") for p in parts):
            continue
        if md.name.startswith("."):
            continue
        yield md


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--input", type=Path, required=True)
    ap.add_argument("--passport", type=Path, required=True)
    ap.add_argument("--rejection-log", dest="rejection_log", type=Path, required=True)
    args = ap.parse_args()

    if not args.input.exists() or not args.input.is_dir():
        print(f"ERROR: vault directory not found: {args.input}", file=sys.stderr)
        return 1

    vault_name = args.input.name
    entries: list[dict] = []
    rejected: list[dict] = []
    existing_keys: set[str] = set()

    for md in iter_markdown_files(args.input):
        accepted, rejection = process_file(md, args.input, vault_name, existing_keys)
        if accepted is not None:
            entries.append(accepted)
        elif rejection is not None:
            rejected.append(rejection)

    write_passport(args.passport, entries)
    write_rejection_log(
        args.rejection_log,
        adapter_name=ADAPTER_NAME,
        adapter_version=ADAPTER_VERSION,
        rejected=rejected,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
