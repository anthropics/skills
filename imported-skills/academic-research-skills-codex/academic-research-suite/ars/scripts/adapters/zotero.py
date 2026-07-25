#!/usr/bin/env python3
"""zotero: produce a literature_corpus passport from a Better BibTeX
Extension JSON export. Reads only local files; does not call the Zotero
Web API.

See design doc §5.3. Users who want a live-sync API-based variant are
expected to write their own adapter using this file as a starting point
(see overview.md extension-point guidance).

Usage:
  python scripts/adapters/zotero.py \
      --input <bbt_export.json> --passport <out.yaml> --rejection-log <out.yaml>
"""
from __future__ import annotations
import argparse
import json
import re
import sys
from pathlib import Path
from typing import NamedTuple

# Allow running as a script: ensure repo root is importable for
# `from scripts.adapters._common import ...`
_THIS = Path(__file__).resolve()
_REPO_ROOT = _THIS.parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from scripts.adapters._common import (  # noqa: E402
    ensure_unique_citekey,
    write_passport,
    write_rejection_log,
    now_iso,
)

ADAPTER_NAME = "zotero.py"
ADAPTER_VERSION = "1.1.0"

# v3.10 (spec §3 PR-B item 13): Zotero item type → venue_type. Zotero's itemType
# is structured source metadata, so this is `adapter_declared` provenance — NOT
# inference from free-form text (R-L3-2-D). Item types not in this map (or absent)
# yield venue_type: unknown + venue_type_provenance: unknown, honoring the §3-PR-B-4
# pair invariant (venue_type present ⟺ provenance present; unknown ⟹ unknown).
ZOTERO_ITEM_TYPE_TO_VENUE_TYPE = {
    "journalArticle": "journal-article",
    "conferencePaper": "conference-paper",
    "book": "book",
    "bookSection": "chapter",
    "thesis": "dissertation",
    "preprint": "preprint",
    "report": "report",
    "dataset": "dataset",
}


def map_venue_type(item_type: str | None) -> tuple[str, str]:
    """Map a Zotero itemType to (venue_type, venue_type_provenance).

    Known structured types map to a declared venue_type with `adapter_declared`
    provenance. Unknown / absent types map to (`unknown`, `unknown`) — the type
    is never guessed from free-form text."""
    vt = ZOTERO_ITEM_TYPE_TO_VENUE_TYPE.get((item_type or "").strip())
    if vt is None:
        return "unknown", "unknown"
    return vt, "adapter_declared"

RE_YEAR = re.compile(r"\b((?:19|20)\d{2})\b")
RE_STRIP_HTML = re.compile(r"<[^>]+>")

# Design doc §410: date strings whose first token is a month or season name
# are ambiguous and must be rejected — the year may be in a non-standard position.
_SEASONAL_PREFIXES = re.compile(
    r"^\s*(?:"
    r"jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|jun(?:e)?"
    r"|jul(?:y)?|aug(?:ust)?|sep(?:tember)?|oct(?:ober)?|nov(?:ember)?|dec(?:ember)?"
    r"|spring|summer|fall|autumn|winter"
    r")\b",
    re.IGNORECASE,
)


class _AuthorsResult(NamedTuple):
    """Structured return from extract_authors — avoids leaking a sentinel into
    the type system while still conveying why the result is empty."""
    authors: list[dict] | None  # None = no valid authors
    had_blank_literal: bool     # True = a corporate-author entry had an empty name


def extract_authors(creators: list[dict]) -> _AuthorsResult:
    """Pull only author-type creators.

    Returns an _AuthorsResult whose ``authors`` field is:
    - A non-empty list when valid authors are found.
    - None otherwise (caller checks ``had_blank_literal`` to distinguish
      "no author-type creators at all" from "blank corporate name").
    """
    out: list[dict] = []
    had_blank_literal = False
    for c in creators or []:
        if c.get("creatorType") != "author":
            continue
        if "name" in c:  # institution / corporate author
            literal = c["name"].strip()
            if not literal:
                # blank name would produce {"literal": ""} which violates the schema
                had_blank_literal = True
                continue
            out.append({"literal": literal})
            continue
        family = (c.get("lastName") or "").strip()
        given = (c.get("firstName") or "").strip()
        if not family:
            continue
        entry: dict[str, str] = {"family": family}
        if given:
            entry["given"] = given
        out.append(entry)
    return _AuthorsResult(authors=out if out else None, had_blank_literal=had_blank_literal)


def extract_year(date_val: str | dict | None) -> int | None:
    """Extract a four-digit year from a date value.

    Accepts:
    - A plain string like "2024", "2024-03", "2024-03-15"
    - A CSL ``issued`` dict like ``{"date-parts": [[2023]]}``

    Returns None for seasonal / month-leading strings ("Spring 2024",
    "January 2024"), strings with no recognizable YYYY pattern, and
    malformed CSL dicts.
    """
    if not date_val:
        return None

    # CSL issued dict: {"date-parts": [[2023, ...]]}
    if isinstance(date_val, dict):
        parts = date_val.get("date-parts")
        if parts and isinstance(parts, list) and parts[0]:
            try:
                return int(parts[0][0])
            except (TypeError, ValueError):
                return None
        return None

    date_str = str(date_val).strip()
    if not date_str:
        return None

    # Reject seasonal / month-leading strings before the year regex fires,
    # since RE_YEAR.search() is unanchored and would accept "Spring 2024".
    if _SEASONAL_PREFIXES.match(date_str):
        return None

    m = RE_YEAR.search(date_str)
    if m:
        return int(m.group(1))
    return None


def strip_doi(doi: str | None) -> str | None:
    if not doi:
        return None
    doi = doi.strip()
    for prefix in ("doi:", "DOI:", "https://doi.org/", "http://doi.org/"):
        if doi.lower().startswith(prefix.lower()):
            doi = doi[len(prefix):]
            break
    return doi.strip() or None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--input", type=Path, required=True, help="BBT JSON export file")
    ap.add_argument("--passport", type=Path, required=True)
    ap.add_argument("--rejection-log", dest="rejection_log", type=Path, required=True)
    args = ap.parse_args()

    try:
        raw = args.input.read_text(encoding="utf-8")
    except FileNotFoundError:
        print(f"ERROR: input not found: {args.input}", file=sys.stderr)
        return 1
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as e:
        print(f"ERROR: input is not valid JSON: {e}", file=sys.stderr)
        return 1
    if not isinstance(data, list):
        print(f"ERROR: expected top-level JSON array, got {type(data).__name__}", file=sys.stderr)
        return 1

    entries: list[dict] = []
    rejected: list[dict] = []
    seen_keys: set[str] = set()

    for item in data:
        citekey = item.get("citationKey") or ""
        item_id = str(item.get("itemID") or "").strip()
        zotero_key = str(item.get("key") or "").strip()
        source_key = item_id or citekey or "<unknown>"

        # Validate all required fields up front; collect every missing field name
        # so the rejection log gives the full picture in one entry.
        missing: list[str] = []

        if not citekey:
            missing.append("citation_key")

        title = (item.get("title") or "").strip()
        if not title:
            missing.append("title")

        authors_result = extract_authors(item.get("creators", []))
        if authors_result.authors is None:
            missing.append("authors")

        # `date` is read first; `issued` (CSL) is the fallback for BBT exports
        # that omit the Zotero `date` field in favour of the CSL form.
        date_val = item.get("date") or item.get("issued")
        year = extract_year(date_val)
        if not year:
            missing.append("year")

        # Design §398-399: source_pointer must be a real Zotero URI — either
        # itemID (numeric, preferred) or the 8-char library key.  @citekey is
        # not a documented Zotero URI form and is rejected.
        if not item_id and not zotero_key:
            missing.append("source_pointer")

        if missing:
            # Preserve backward-compatible reason strings for the single-field
            # cases that existing callers already test against.
            if missing == ["authors"] and not authors_result.had_blank_literal:
                reason = "authors_unparseable"
            elif missing == ["year"]:
                reason = "year_unparseable"
            else:
                reason = "missing_required_field"
            rejected.append({
                "source": source_key,
                "reason": reason,
                "raw": item,
                "missing_fields": missing,
            })
            continue

        # Both branches below are only reached when missing is empty, so all
        # required fields are guaranteed valid at this point.
        final_key = ensure_unique_citekey(citekey, seen_keys)

        source_pointer = (
            f"zotero://select/items/0_{item_id}"
            if item_id
            else f"zotero://select/items/{zotero_key}"
        )

        venue = (
            item.get("publicationTitle")
            or item.get("proceedingsTitle")
            or item.get("bookTitle")
            or None
        )

        entry: dict = {
            "citation_key": final_key,
            "title": title,
            "authors": authors_result.authors,
            "year": year,
            "source_pointer": source_pointer,
            "obtained_via": "zotero-bbt-export",
            "obtained_at": now_iso(),
            "adapter_name": ADAPTER_NAME,
            "adapter_version": ADAPTER_VERSION,
        }
        if venue:
            entry["venue"] = venue
        # v3.10: declare venue_type from the structured Zotero itemType. Always
        # emit the pair together (venue_type + venue_type_provenance) so the
        # schema pair-invariant holds; unknown types declare unknown/unknown.
        venue_type, venue_type_provenance = map_venue_type(item.get("itemType"))
        entry["venue_type"] = venue_type
        entry["venue_type_provenance"] = venue_type_provenance
        doi = strip_doi(item.get("DOI"))
        if doi:
            entry["doi"] = doi
        tags = [t.get("tag") for t in item.get("tags", []) if t.get("tag")]
        if tags:
            entry["tags"] = tags
        abstract = item.get("abstractNote")
        if abstract:
            entry["abstract"] = abstract
        notes = item.get("notes") or []
        if notes:
            plain = "\n\n".join(
                RE_STRIP_HTML.sub("", n.get("note", ""))
                for n in notes
                if n.get("note")
            )
            if plain.strip():
                entry["user_notes"] = plain

        entries.append(entry)

    write_passport(args.passport, entries)
    # input_source is intentionally omitted: it is a machine-dependent absolute
    # path that would make the golden fixture non-portable. The rejection log
    # schema marks input_source as optional precisely for this use case.
    write_rejection_log(
        args.rejection_log,
        adapter_name=ADAPTER_NAME,
        adapter_version=ADAPTER_VERSION,
        rejected=rejected,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
