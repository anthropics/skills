"""Minimal RIS, BibTeX, NBIB, and CSV citation import helpers."""

from __future__ import annotations

import csv
import io
import re
from typing import Any

from ..domain.identifiers import normalize_doi, normalize_pmid


def parse_citation_records(content: str, fmt: str) -> list[dict[str, Any]]:
    fmt = fmt.lower().strip()
    if fmt == "ris":
        return _parse_ris(content)
    if fmt == "bibtex":
        return _parse_bibtex(content)
    if fmt == "nbib":
        return _parse_nbib(content)
    if fmt == "csv":
        return _parse_csv(content)
    raise ValueError(f"Unsupported input format: {fmt}")


def _parse_ris(content: str) -> list[dict[str, Any]]:
    records = []
    current: dict[str, Any] = {"authors": [], "external_ids": {}}
    for raw_line in content.splitlines():
        if len(raw_line) < 6 or "  - " not in raw_line:
            continue
        tag, value = raw_line.split("  - ", 1)
        value = value.strip()
        if tag == "ER":
            if _has_content(current):
                records.append(_finalize(current))
            current = {"authors": [], "external_ids": {}}
        elif tag in {"TI", "T1"}:
            current["title"] = value
        elif tag == "AU":
            current.setdefault("authors", []).append(value)
        elif tag in {"JO", "JF", "T2"} and not current.get("journal"):
            current["journal"] = value
        elif tag in {"PY", "Y1"}:
            current["year"] = _year(value)
        elif tag == "DO":
            current["doi"] = value
    if _has_content(current):
        records.append(_finalize(current))
    return records


def _parse_bibtex(content: str) -> list[dict[str, Any]]:
    records = []
    for match in re.finditer(r"@\w+\s*\{[^,]+,(.*?)\n\}", content, flags=re.DOTALL):
        body = match.group(1)
        fields = {key.lower(): value for key, value in re.findall(r"(\w+)\s*=\s*[\{\"](.+?)[\}\"]\s*,?", body, flags=re.DOTALL)}
        record = {
            "title": _clean(fields.get("title")),
            "authors": [_clean(author) for author in re.split(r"\s+and\s+", fields.get("author", "")) if _clean(author)],
            "journal": _clean(fields.get("journal") or fields.get("journaltitle")),
            "year": _year(fields.get("year")),
            "doi": _clean(fields.get("doi")),
            "external_ids": {},
        }
        records.append(_finalize(record))
    return records


def _parse_nbib(content: str) -> list[dict[str, Any]]:
    records = []
    current: dict[str, Any] = {"authors": [], "external_ids": {}}
    for raw_line in content.splitlines():
        if len(raw_line) < 6 or "- " not in raw_line[:6]:
            continue
        tag = raw_line[:4].strip()
        value = raw_line[6:].strip()
        if tag == "PMID" and _has_content(current):
            records.append(_finalize(current))
            current = {"authors": [], "external_ids": {}}
        if tag == "PMID":
            current.setdefault("external_ids", {})["pmid"] = normalize_pmid(value)
        elif tag == "TI":
            current["title"] = value.rstrip(".")
        elif tag in {"FAU", "AU"}:
            current.setdefault("authors", []).append(value)
        elif tag == "JT":
            current["journal"] = value
        elif tag == "DP":
            current["year"] = _year(value)
        elif tag == "AID" and "[doi]" in value.lower():
            current["doi"] = value.split()[0]
    if _has_content(current):
        records.append(_finalize(current))
    return records


def _parse_csv(content: str) -> list[dict[str, Any]]:
    reader = csv.DictReader(io.StringIO(content))
    records = []
    for row in reader:
        authors = row.get("authors") or row.get("author") or ""
        records.append(
            _finalize(
                {
                    "title": row.get("title") or row.get("Title") or "",
                    "authors": [_clean(author) for author in re.split(r";|\band\b", authors) if _clean(author)],
                    "doi": row.get("doi") or row.get("DOI") or "",
                    "year": _year(row.get("year") or row.get("Year")),
                    "journal": row.get("journal") or row.get("Journal") or "",
                    "external_ids": {},
                }
            )
        )
    return records


def _finalize(record: dict[str, Any]) -> dict[str, Any]:
    record = dict(record)
    doi = normalize_doi(record.get("doi"))
    record["doi"] = doi or ""
    if doi:
        record.setdefault("external_ids", {})["doi"] = doi
    record["authors"] = list(record.get("authors") or [])
    return record


def _has_content(record: dict[str, Any]) -> bool:
    return bool(record.get("title") or record.get("doi") or record.get("external_ids"))


def _year(value: Any) -> int | None:
    match = re.search(r"\d{4}", str(value or ""))
    return int(match.group(0)) if match else None


def _clean(value: Any) -> str:
    return " ".join(str(value or "").replace("\n", " ").split())
