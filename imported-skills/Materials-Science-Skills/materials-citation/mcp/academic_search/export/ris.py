"""RIS format citation export.

RIS is the standard import format for EndNote, Zotero, Mendeley, and most
reference managers.  Each record is a block of two-letter tagged lines
terminated by ``ER  -``.
"""

from __future__ import annotations

import re
from typing import Any


def build_ris_record(record: dict[str, Any]) -> str:
    """Convert a single metadata record to an RIS block."""
    lines: list[str] = []
    _tag(lines, "TY", "JOUR")
    _tag(lines, "TI", record.get("title", ""))
    for author in record.get("authors") or []:
        _tag(lines, "AU", author)
    journal = record.get("journal", "")
    _tag(lines, "JO", journal)
    _tag(lines, "T2", journal)
    year = record.get("year")
    if year:
        _tag(lines, "PY", str(year))
        _tag(lines, "Y1", f"{year}///")
    _tag(lines, "VL", record.get("volume", ""))
    _tag(lines, "IS", record.get("issue", ""))
    pages = record.get("pages", "")
    if pages:
        if "-" in str(pages):
            sp, ep = str(pages).split("-", 1)
            _tag(lines, "SP", sp.strip())
            _tag(lines, "EP", ep.strip())
        else:
            _tag(lines, "SP", str(pages))
    doi = record.get("doi", "")
    _tag(lines, "DO", doi)
    if doi:
        _tag(lines, "UR", f"https://doi.org/{doi}")
    _tag(lines, "SN", record.get("issn", ""))
    _tag(lines, "N1", "Exported by materials-academic-search.")
    lines.append("ER  -")
    lines.append("")
    return "\n".join(lines)


def build_ris_file(records: list[dict[str, Any]]) -> str:
    """Build a complete RIS file from multiple records."""
    return "".join(build_ris_record(r) for r in records)


def _tag(lines: list[str], tag: str, value: str) -> None:
    cleaned = _ris_escape(value)
    if cleaned:
        lines.append(f"{tag}  - {cleaned}")


def _ris_escape(text: str) -> str:
    """Strip HTML tags and normalize whitespace for RIS safety."""
    text = re.sub(r"<[^>]+>", " ", str(text))
    text = text.replace("\n", " ").replace("\r", " ")
    return " ".join(text.split())
