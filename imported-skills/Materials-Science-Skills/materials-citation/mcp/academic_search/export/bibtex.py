"""BibTeX format citation export.

BibTeX is the standard format for LaTeX users.  Each record is an
``@article{key, ...}`` block with brace-delimited fields.
"""

from __future__ import annotations

import re
from typing import Any


def build_bibtex_entry(record: dict[str, Any]) -> str:
    """Convert a single metadata record to a BibTeX entry."""
    key = _citation_key(record)
    fields: list[str] = []

    title = record.get("title", "")
    if title:
        fields.append(f"  title     = {{{_bibtex_escape(title)}}}")

    authors = record.get("authors") or []
    if authors:
        fields.append(f"  author    = {{{_bibtex_escape(' and '.join(authors))}}}")

    journal = record.get("journal", "")
    if journal:
        fields.append(f"  journal   = {{{_bibtex_escape(journal)}}}")

    year = record.get("year")
    if year:
        fields.append(f"  year      = {{{year}}}")

    volume = record.get("volume", "")
    if volume:
        fields.append(f"  volume    = {{{volume}}}")

    issue = record.get("issue", "")
    if issue:
        fields.append(f"  number    = {{{issue}}}")

    pages = record.get("pages", "")
    if pages:
        fields.append(f"  pages     = {{{pages}}}")

    doi = record.get("doi", "")
    if doi:
        fields.append(f"  doi       = {{{doi}}}")
        fields.append(f"  url       = {{https://doi.org/{doi}}}")

    issn = record.get("issn", "")
    if issn:
        fields.append(f"  issn      = {{{issn}}}")

    body = ",\n".join(fields)
    return f"@article{{{key},\n{body}\n}}"


def build_bibtex_file(records: list[dict[str, Any]]) -> str:
    """Build a complete BibTeX file from multiple records."""
    entries = [build_bibtex_entry(r) for r in records]
    return "\n\n".join(entries) + "\n"


def _citation_key(record: dict[str, Any]) -> str:
    """Generate a citation key: first_author_surname + year + first_title_word."""
    authors = record.get("authors") or []
    surname = "unknown"
    if authors:
        first = authors[0]
        # "Given Family" or "Family, Given"
        parts = first.strip().split()
        surname = parts[-1] if parts else "unknown"
    surname = re.sub(r"[^a-zA-Z]", "", surname).lower()

    year = record.get("year") or "0000"

    title = record.get("title", "")
    title_words = re.findall(r"[a-zA-Z]+", title)
    first_word = title_words[0].lower() if title_words else "untitled"

    return f"{surname}{year}{first_word}"


def _bibtex_escape(text: str) -> str:
    """Escape special BibTeX characters."""
    text = re.sub(r"<[^>]+>", " ", str(text))
    text = " ".join(text.split())
    # BibTeX is fragile with these characters inside braces
    for ch in ("&", "%", "#", "_"):
        text = text.replace(ch, f"\\{ch}")
    return text
