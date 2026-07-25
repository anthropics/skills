"""Optional Scopus Search/Abstract adapter."""

from __future__ import annotations

from typing import Any, Callable
from urllib.parse import quote

from .base import normalize_doi
from .elsevier_common import creator_names, elsevier_headers, get_elsevier_json, int_or_none, require_api_key, year_from_cover_date
from ..domain.identifiers import normalize_scopus_eid


class ScopusAdapter:
    name = "scopus"
    search_url = "https://api.elsevier.com/content/search/scopus"
    abstract_url = "https://api.elsevier.com/content/abstract"

    def __init__(self, *, timeout: float = 20.0, getter: Callable[..., Any] | None = None) -> None:
        self.timeout = timeout
        self.getter = getter
        self.api_key = require_api_key("SCOPUS_API_KEY", "Scopus")

    def search(self, query: str, *, journals=None, year_range: str | None = None, limit: int = 10) -> list[dict[str, Any]]:
        params: dict[str, Any] = {"query": _query_with_years(query, year_range), "count": max(1, min(int(limit), 25))}
        payload = get_elsevier_json("Scopus", self.search_url, params=params, headers=elsevier_headers(self.api_key), timeout=self.timeout, getter=self.getter)
        return [_parse_entry(item) for item in payload.get("search-results", {}).get("entry", [])]

    def fetch(self, *, doi: str | None = None, title: str | None = None, external_id: str | None = None) -> dict[str, Any] | None:
        eid = normalize_scopus_eid(external_id) if external_id else None
        if eid:
            url = f"{self.abstract_url}/eid/{quote(eid, safe='')}"
        elif doi:
            url = f"{self.abstract_url}/doi/{quote(normalize_doi(doi), safe='')}"
        else:
            return None
        payload = get_elsevier_json("Scopus", url, headers=elsevier_headers(self.api_key), timeout=self.timeout, getter=self.getter)
        coredata = (payload.get("abstracts-retrieval-response") or {}).get("coredata") or payload.get("coredata") or {}
        return _parse_entry(coredata)


def _query_with_years(query: str, year_range: str | None) -> str:
    if year_range and "-" in str(year_range):
        start, end = [part.strip() for part in str(year_range).split("-", 1)]
        if start and end:
            return f"{query} AND PUBYEAR > {int(start) - 1} AND PUBYEAR < {int(end) + 1}"
    return query


def _parse_entry(item: dict[str, Any]) -> dict[str, Any]:
    eid = normalize_scopus_eid(item.get("eid") or item.get("dc:identifier"))
    doi = normalize_doi(item.get("prism:doi"))
    url = item.get("prism:url") or item.get("link", [{}])[0].get("@href", "") if isinstance(item.get("link"), list) else item.get("prism:url", "")
    return {
        "title": item.get("dc:title") or item.get("title") or "",
        "doi": doi,
        "journal": item.get("prism:publicationName") or item.get("publicationName") or "",
        "year": year_from_cover_date(item.get("prism:coverDate") or item.get("coverDate")),
        "authors": creator_names(item.get("dc:creator")),
        "abstract": item.get("dc:description") or item.get("description") or "",
        "citation_count": int_or_none(item.get("citedby-count")),
        "url": url,
        "source": "scopus",
        "external_ids": {key: value for key, value in {"scopus_eid": eid, "doi": doi}.items() if value},
    }
