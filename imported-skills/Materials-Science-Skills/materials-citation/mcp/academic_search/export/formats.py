"""Unified citation export dispatcher.

Supports RIS, BibTeX, and GB/T 7714 (Chinese national standard) formats.
For APA/Nature/IEEE, use CrossRef content negotiation at the service layer.
"""

from __future__ import annotations

import re
from typing import Any

from .bibtex import build_bibtex_file
from .csl_json import build_csl_json
from .jsonl import build_jsonl
from .ris import build_ris_file

SUPPORTED_FORMATS = ("ris", "bibtex", "gbt7714", "csl-json", "jsonl")


def export_citations(records: list[dict[str, Any]], fmt: str) -> str:
    """Export records in the requested format.

    Parameters
    ----------
    records : list of dict
        Each dict must have at least ``title`` and ``authors``.
        Optional: ``doi``, ``journal``, ``year``, ``volume``, ``issue``,
        ``pages``, ``issn``.
    fmt : str
        One of ``ris``, ``bibtex``, ``gbt7714``, ``csl-json``, or ``jsonl``.

    Returns
    -------
    str
        The formatted citation file content.
    """
    fmt = fmt.lower().strip()
    if fmt == "ris":
        return build_ris_file(records)
    if fmt == "bibtex":
        return build_bibtex_file(records)
    if fmt == "gbt7714":
        return build_gbt7714_file(records)
    if fmt == "csl-json":
        return build_csl_json(records)
    if fmt == "jsonl":
        return build_jsonl(records)
    raise ValueError(f"Unsupported format: {fmt!r}. Use one of {SUPPORTED_FORMATS}")


# ---------------------------------------------------------------------------
# GB/T 7714 — Chinese national standard for bibliographic references
# Uses numbered style [1], [2], ... with specific formatting rules.
# ---------------------------------------------------------------------------


def build_gbt7714_entry(record: dict[str, Any], number: int) -> str:
    """Build a single GB/T 7714 formatted reference.

    Format (journal article, sequential numbering):
        [1] AUTHORS. TITLE[J]. JOURNAL, YEAR, VOLUME(ISSUE): PAGES.
    """
    parts: list[str] = []

    # Authors: surname uppercase, given name initial
    authors = record.get("authors") or []
    if authors:
        formatted = [_gbt7714_author(a) for a in authors]
        if len(formatted) > 3:
            parts.append(", ".join(formatted[:3]) + ", et al")
        else:
            parts.append(", ".join(formatted))
    else:
        parts.append("[Author unknown]")

    # Title
    title = _clean(record.get("title", ""))
    parts.append(f"{title}[J]")

    # Journal, Year, Volume(Issue): Pages
    journal = _clean(record.get("journal", ""))
    year = record.get("year") or ""
    volume = record.get("volume", "")
    issue = record.get("issue", "")
    pages = record.get("pages", "")

    detail_parts = []
    if journal:
        detail_parts.append(journal)
    if year:
        detail_parts.append(str(year))
    vol_issue = ""
    if volume:
        vol_issue = str(volume)
        if issue:
            vol_issue += f"({issue})"
    if vol_issue:
        detail_parts.append(vol_issue)
    if pages:
        detail_parts.append(str(pages))

    if detail_parts:
        parts.append(", ".join(detail_parts) + ".")

    # DOI
    doi = record.get("doi", "")
    if doi:
        parts.append(f"DOI: {doi}.")

    return f"[{number}] " + " ".join(parts)


def build_gbt7714_file(records: list[dict[str, Any]]) -> str:
    """Build a complete GB/T 7714 reference list."""
    lines = []
    for i, record in enumerate(records, 1):
        lines.append(build_gbt7714_entry(record, i))
    return "\n".join(lines) + "\n"


def _gbt7714_author(name: str) -> str:
    """Format a single author name for GB/T 7714: SURNAME GivenInitials.

    Input can be "Given Family" or "Family, Given".
    """
    name = name.strip()
    if "," in name:
        family, given = [p.strip() for p in name.split(",", 1)]
    else:
        parts = name.split()
        if len(parts) < 2:
            return name.upper()
        given = " ".join(parts[:-1])
        family = parts[-1]

    family = family.upper()
    # Initials: take first letter of each given-name part
    initials = "".join(p[0].upper() + "." for p in given.split() if p)
    if initials:
        return f"{family} {initials}"
    return family


def _clean(text: str) -> str:
    """Strip HTML tags and normalize whitespace."""
    text = re.sub(r"<[^>]+>", " ", str(text))
    return " ".join(text.split())
