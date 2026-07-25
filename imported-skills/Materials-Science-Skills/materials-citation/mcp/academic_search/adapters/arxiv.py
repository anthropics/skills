"""arXiv Atom API adapter."""

from __future__ import annotations

import re
import xml.etree.ElementTree as ET
from typing import Any, Callable

import httpx

from .base import AdapterError, clean_abstract, get_response_with_retries, normalize_doi
from ..domain.identifiers import canonical_arxiv_id, normalize_arxiv_id


class ArxivAdapter:
    name = "arxiv"
    base_url = "https://export.arxiv.org/api/query"

    def __init__(self, *, timeout: float = 20.0, getter: Callable[..., Any] | None = None) -> None:
        self.timeout = timeout
        self.getter = getter or get_response_with_retries

    def search(self, query: str, *, journals=None, year_range: str | None = None, limit: int = 10) -> list[dict[str, Any]]:
        params = {
            "search_query": _query_with_year_range(query, year_range),
            "start": 0,
            "max_results": max(1, min(int(limit), 50)),
            "sortBy": "submittedDate",
            "sortOrder": "descending",
        }
        try:
            response = self.getter(self.base_url, params=params, timeout=self.timeout)
            response.raise_for_status()
        except httpx.HTTPError as exc:
            raise AdapterError(f"arXiv search failed: {exc}") from exc
        return _parse_atom_feed(response.text)

    def fetch(self, *, doi: str | None = None, title: str | None = None, external_id: str | None = None) -> dict[str, Any] | None:
        arxiv_id = normalize_arxiv_id(external_id) if external_id else None
        if arxiv_id:
            params = {"id_list": arxiv_id, "max_results": 1}
        elif title:
            params = {"search_query": f'ti:"{title}"', "max_results": 1}
        else:
            return None
        try:
            response = self.getter(self.base_url, params=params, timeout=self.timeout)
            response.raise_for_status()
        except httpx.HTTPError as exc:
            raise AdapterError(f"arXiv fetch failed: {exc}") from exc
        records = _parse_atom_feed(response.text)
        return records[0] if records else None


def _query_with_year_range(query: str, year_range: str | None) -> str:
    text = f"all:{query}"
    if year_range and "-" in str(year_range):
        start, end = [part.strip() for part in str(year_range).split("-", 1)]
        if start and end:
            text += f" AND submittedDate:[{start}01010000 TO {end}12312359]"
    return text


def _parse_atom_feed(text: str) -> list[dict[str, Any]]:
    ns = {"atom": "http://www.w3.org/2005/Atom", "arxiv": "http://arxiv.org/schemas/atom"}
    root = ET.fromstring(text)
    records = []
    for entry in root.findall("atom:entry", ns):
        raw_id = _text(entry, "atom:id", ns)
        arxiv_id = normalize_arxiv_id(raw_id) or ""
        doi = normalize_doi(_text(entry, "arxiv:doi", ns))
        published = _text(entry, "atom:published", ns) or _text(entry, "atom:updated", ns)
        url = _alternate_url(entry, ns) or (f"https://arxiv.org/abs/{arxiv_id}" if arxiv_id else raw_id)
        records.append(
            {
                "title": _clean_title(_text(entry, "atom:title", ns)),
                "doi": doi,
                "journal": "arXiv",
                "year": _year(published),
                "authors": [_text(author, "atom:name", ns) for author in entry.findall("atom:author", ns) if _text(author, "atom:name", ns)],
                "abstract": clean_abstract(_text(entry, "atom:summary", ns)),
                "url": url,
                "source": "arxiv",
                "external_ids": {
                    "arxiv": arxiv_id,
                    "arxiv_canonical": canonical_arxiv_id(arxiv_id),
                    **({"doi": doi} if doi else {}),
                },
                "source_provenance": [{"source": "arxiv", "url": url, "external_ids": {"arxiv": arxiv_id}}],
            }
        )
    return records


def _text(element: ET.Element, path: str, ns: dict[str, str]) -> str:
    found = element.find(path, ns)
    return (found.text or "").strip() if found is not None else ""


def _alternate_url(entry: ET.Element, ns: dict[str, str]) -> str:
    for link in entry.findall("atom:link", ns):
        if link.attrib.get("rel") == "alternate" and link.attrib.get("href"):
            return link.attrib["href"]
    return ""


def _clean_title(value: str) -> str:
    return " ".join(value.split())


def _year(value: str) -> int | None:
    match = re.search(r"\d{4}", value or "")
    return int(match.group(0)) if match else None
