#!/usr/bin/env python3
"""folder_scan: produce a literature_corpus passport from a directory of
files (typically PDFs). Parses citation metadata from filenames using
best-effort conventions. Never parses PDF content.

Filename conventions recognized:
  - {Family}_{Year}_{title_slug}.{ext}  (underscore-separated)
  - {Family}{Year}{optional_title_slug}.{ext}  (concatenated)
  - fallback: first capitalized Latin word before the year.

Files whose filename cannot be parsed for both family and year are rejected.
Non-Latin filenames (e.g. CJK characters) are rejected; Unicode filename
support is a future extension opportunity.

Usage:
  python scripts/adapters/folder_scan.py \\
      --input <dir> --passport <out.yaml> --rejection-log <out.yaml>
"""
from __future__ import annotations
import argparse
import re
import sys
from pathlib import Path

# Allow running as a script: ensure repo root is importable for
# `from scripts.adapters._common import ...`
_THIS = Path(__file__).resolve()
_REPO_ROOT = _THIS.parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from scripts.adapters._common import (  # noqa: E402
    make_citation_key,
    path_to_file_uri,
    write_passport,
    write_rejection_log,
    now_iso,
)

ADAPTER_NAME = "folder_scan.py"
ADAPTER_VERSION = "1.1.0"

# Family_Year_title style: "Wang_2023_formative_feedback.pdf"
RE_FAMILY_UNDERSCORE = re.compile(
    r"^([A-Z][A-Za-z]*)_((?:19|20)\d{2})(?:_(.*?))?\.[A-Za-z0-9]+$"
)
# Family{Year} style: "Chen2024_AIAssessment.pdf" or "Chen2024.pdf"
RE_FAMILY_YEAR = re.compile(
    r"^([A-Z][A-Za-z]*)((?:19|20)\d{2})[_\-.\s]?(.*?)\.[A-Za-z0-9]+$"
)
# fallback year anywhere
RE_ANY_YEAR = re.compile(r"((?:19|20)\d{2})")
RE_FIRST_CAPITAL = re.compile(r"\b([A-Z][A-Za-z]+)\b")

# Reject entries with any non-ASCII char in the filename
RE_NON_ASCII = re.compile(r"[^\x00-\x7f]")


def parse_filename(name: str) -> dict | None:
    """Return {'family', 'year', 'title', 'title_hint'} or None if unparseable.

    `title` is the human-facing title written into the passport entry.
    `title_hint` is the substring used to derive the citation_key's
    third component — it MUST exclude the family token, otherwise
    make_citation_key would produce keys like ``chen2024chen``.
    """
    if RE_NON_ASCII.search(name):
        return None

    m = RE_FAMILY_UNDERSCORE.match(name)
    if m:
        family = m.group(1)
        year = int(m.group(2))
        tail = (m.group(3) or "").strip()
        tail_words = tail.replace("_", " ").strip()
        title = f"{family} {year} {tail_words}".strip()
        return {
            "family": family,
            "year": year,
            "title": title,
            "title_hint": tail_words,
        }

    m = RE_FAMILY_YEAR.match(name)
    if m:
        family = m.group(1)
        year = int(m.group(2))
        tail = (m.group(3) or "").strip()
        stem = Path(name).stem
        # Display title keeps the original stem layout (with _ → space).
        title = stem.replace("_", " ")
        return {
            "family": family,
            "year": year,
            "title": title,
            "title_hint": tail.replace("_", " "),
        }

    year_match = RE_ANY_YEAR.search(name)
    if year_match:
        before_year = name.split(year_match.group(1))[0]
        fam_match = RE_FIRST_CAPITAL.search(before_year)
        if fam_match:
            return {
                "family": fam_match.group(1),
                "year": int(year_match.group(1)),
                "title": Path(name).stem.replace("_", " "),
                "title_hint": "",
            }
    return None


def _missing_fields_for(name: str) -> list[str]:
    """Diagnostic for the rejection_log."""
    if RE_NON_ASCII.search(name):
        return ["authors"]
    if not RE_ANY_YEAR.search(name):
        return ["authors", "year"]
    return ["authors"]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--input", type=Path, required=True, help="Directory to scan")
    ap.add_argument("--passport", type=Path, required=True)
    ap.add_argument(
        "--rejection-log", dest="rejection_log", type=Path, required=True
    )
    args = ap.parse_args()

    if not args.input.exists() or not args.input.is_dir():
        print(
            f"ERROR: input directory not found: {args.input}", file=sys.stderr
        )
        return 1

    entries: list[dict] = []
    rejected: list[dict] = []
    existing_keys: set[str] = set()

    input_root = args.input.resolve()
    files = sorted(
        p for p in args.input.rglob("*") if p.is_file() and p.name != ".gitkeep"
    )
    for f in files:
        # Use path relative to --input so two files with the same basename
        # in different subdirectories remain distinguishable in both the
        # passport (via source_pointer) and the rejection log.
        try:
            rel = f.relative_to(args.input)
        except ValueError:
            # Defensive: rglob shouldn't yield this, but fall back to
            # basename if it ever does.
            rel = Path(f.name)
        rel_str = rel.as_posix()
        if f.is_symlink():
            try:
                f.resolve().relative_to(input_root)
            except ValueError:
                rejected.append({
                    "source": rel_str,
                    "reason": "other",
                    "detail": "symlink resolves outside the input root",
                    "raw": rel_str,
                    "missing_fields": [],
                })
                continue
        parsed = parse_filename(f.name)
        if not parsed:
            rejected.append({
                "source": rel_str,
                "reason": "authors_unparseable",
                "raw": rel_str,
                "missing_fields": _missing_fields_for(f.name),
            })
            continue

        citation_key = make_citation_key(
            family=parsed["family"],
            year=parsed["year"],
            title_hint=parsed["title_hint"],
            existing=existing_keys,
        )
        entries.append({
            "citation_key": citation_key,
            "title": parsed["title"],
            "authors": [{"family": parsed["family"]}],
            "year": parsed["year"],
            "source_pointer": path_to_file_uri(f),
            "obtained_via": "folder-scan",
            "obtained_at": now_iso(),
            "adapter_name": ADAPTER_NAME,
            "adapter_version": ADAPTER_VERSION,
            # v3.10 (spec §3 PR-B item 13): a filename scan carries no structured
            # source-type metadata, so venue_type is always unknown/unknown —
            # never inferred from the filename (R-L3-2-D). Emitted as a pair to
            # honor the schema pair invariant.
            "venue_type": "unknown",
            "venue_type_provenance": "unknown",
        })

    write_passport(args.passport, entries)
    write_rejection_log(
        args.rejection_log,
        adapter_name=ADAPTER_NAME,
        adapter_version=ADAPTER_VERSION,
        rejected=rejected,
        input_source=str(args.input),
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
