"""Semantic Scholar Academic Graph adapter."""

from __future__ import annotations

import os
from typing import Any
from urllib.parse import quote

import httpx

from .base import AdapterError, get_json_with_retries, get_response_with_retries, normalize_doi


class SemanticScholarAdapter:
    name = "Semantic Scholar"
    base_url = "https://api.semanticscholar.org/graph/v1"
    fields = "title,authors,year,journal,abstract,externalIds,citationCount,url"

    def __init__(self, *, timeout: float = 20.0) -> None:
        self.timeout = timeout
        self.api_key = os.getenv("SEMANTIC_SCHOLAR_API_KEY", "").strip()

    def search(self, query: str, *, journals=None, year_range: str | None = None, limit: int = 10) -> list[dict[str, Any]]:
        params: dict[str, Any] = {
            "query": query,
            "limit": max(1, min(int(limit), 50)),
            "fields": self.fields,
        }
        if year_range:
            params["year"] = year_range
        try:
            payload = get_json_with_retries(
                f"{self.base_url}/paper/search",
                params=params,
                headers=self._headers(),
                timeout=self.timeout,
            )
            items = payload.get("data", [])
        except httpx.HTTPError as exc:
            raise AdapterError(f"Semantic Scholar search failed: {exc}") from exc
        return [_parse_paper(item) for item in items]

    def fetch(self, *, doi: str | None = None, title: str | None = None, external_id: str | None = None) -> dict[str, Any] | None:
        paper_id = external_id or (f"DOI:{normalize_doi(doi)}" if doi else None)
        if not paper_id:
            return None
        try:
            response = get_response_with_retries(
                f"{self.base_url}/paper/{quote(paper_id, safe=':')}",
                params={"fields": self.fields},
                headers=self._headers(),
                timeout=self.timeout,
            )
            if response.status_code == 404:
                return None
            response.raise_for_status()
            item = response.json()
        except httpx.HTTPError as exc:
            raise AdapterError(f"Semantic Scholar fetch failed: {exc}") from exc
        return _parse_paper(item)

    def _headers(self) -> dict[str, str]:
        return {"x-api-key": self.api_key} if self.api_key else {}


def _parse_paper(item: dict[str, Any]) -> dict[str, Any]:
    external_ids = item.get("externalIds") or {}
    journal = item.get("journal") or {}
    return {
        "title": item.get("title") or "",
        "doi": normalize_doi(external_ids.get("DOI")),
        "journal": journal.get("name") if isinstance(journal, dict) else "",
        "year": item.get("year"),
        "authors": [author.get("name", "") for author in item.get("authors", []) if author.get("name")],
        "abstract": item.get("abstract") or "",
        "citation_count": item.get("citationCount"),
        "url": item.get("url") or "",
        "source": "Semantic Scholar",
        "external_ids": {
            "semantic_scholar": item.get("paperId"),
            "doi": normalize_doi(external_ids.get("DOI")),
        },
    }
