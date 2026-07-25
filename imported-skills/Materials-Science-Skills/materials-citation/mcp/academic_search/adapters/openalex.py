"""OpenAlex Works API adapter."""

from __future__ import annotations

import os
from typing import Any

import httpx

from .base import AdapterDisabled, AdapterError, clean_abstract, get_json_with_retries, get_response_with_retries, normalize_doi


class OpenAlexAdapter:
    name = "OpenAlex"
    base_url = "https://api.openalex.org/works"

    def __init__(self, *, timeout: float = 20.0) -> None:
        self.timeout = timeout
        self.api_key = os.getenv("OPENALEX_API_KEY", "").strip()

    def search(self, query: str, *, journals=None, year_range: str | None = None, limit: int = 10) -> list[dict[str, Any]]:
        if not self.api_key:
            raise AdapterDisabled("OpenAlex skipped because OPENALEX_API_KEY is not set.")
        params: dict[str, Any] = {
            "search": query,
            "per-page": max(1, min(int(limit), 50)),
            "select": "id,doi,title,display_name,publication_year,primary_location,authorships,abstract_inverted_index,cited_by_count",
            "api_key": self.api_key,
        }
        filters = _year_filter(year_range)
        if filters:
            params["filter"] = filters
        try:
            payload = get_json_with_retries(self.base_url, params=params, timeout=self.timeout)
            items = payload.get("results", [])
        except httpx.HTTPError as exc:
            raise AdapterError(f"OpenAlex search failed: {exc}") from exc
        return [_parse_work(item) for item in items]

    def fetch(self, *, doi: str | None = None, title: str | None = None, external_id: str | None = None) -> dict[str, Any] | None:
        if not self.api_key:
            raise AdapterDisabled("OpenAlex skipped because OPENALEX_API_KEY is not set.")
        identifier = external_id or (f"https://doi.org/{normalize_doi(doi)}" if doi else None)
        if not identifier:
            return None
        try:
            response = get_response_with_retries(
                f"{self.base_url}/{identifier}",
                params={"api_key": self.api_key},
                timeout=self.timeout,
            )
            if response.status_code == 404:
                return None
            response.raise_for_status()
            item = response.json()
        except httpx.HTTPError as exc:
            raise AdapterError(f"OpenAlex fetch failed: {exc}") from exc
        return _parse_work(item)


def _year_filter(year_range: str | None) -> str:
    if not year_range or "-" not in str(year_range):
        return ""
    start, end = [part.strip() for part in str(year_range).split("-", 1)]
    filters = []
    if start:
        filters.append(f"from_publication_date:{start}-01-01")
    if end:
        filters.append(f"to_publication_date:{end}-12-31")
    return ",".join(filters)


def _abstract_from_inverted_index(value: dict[str, list[int]] | None) -> str:
    if not value:
        return ""
    positions: dict[int, str] = {}
    for word, indexes in value.items():
        for index in indexes:
            positions[index] = word
    return " ".join(positions[index] for index in sorted(positions))


def _parse_work(item: dict[str, Any]) -> dict[str, Any]:
    location = item.get("primary_location") or {}
    source = location.get("source") or {}
    authors = []
    for authorship in item.get("authorships", []) or []:
        author = authorship.get("author") or {}
        if author.get("display_name"):
            authors.append(author["display_name"])
    doi = normalize_doi(item.get("doi"))
    return {
        "title": item.get("title") or item.get("display_name") or "",
        "doi": doi,
        "journal": source.get("display_name") or "",
        "year": item.get("publication_year"),
        "authors": authors,
        "abstract": clean_abstract(_abstract_from_inverted_index(item.get("abstract_inverted_index"))),
        "citation_count": item.get("cited_by_count"),
        "url": item.get("id") or "",
        "source": "OpenAlex",
        "external_ids": {"openalex": item.get("id"), "doi": doi},
    }
