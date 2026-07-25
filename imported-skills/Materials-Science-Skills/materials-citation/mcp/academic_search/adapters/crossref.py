"""Crossref REST API adapter."""

from __future__ import annotations

import os
from typing import Any
from urllib.parse import quote

import httpx

from .base import AdapterError, clean_abstract, first_value, get_json_with_retries, get_response_with_retries, normalize_doi


class CrossrefAdapter:
    name = "Crossref"
    base_url = "https://api.crossref.org"

    def __init__(self, *, timeout: float = 20.0) -> None:
        self.timeout = timeout
        self.mailto = os.getenv("MATERIALS_CONTACT_EMAIL", "").strip()

    def search(self, query: str, *, journals=None, year_range: str | None = None, limit: int = 10) -> list[dict[str, Any]]:
        params: dict[str, Any] = {
            "query.bibliographic": query,
            "rows": max(1, min(int(limit), 50)),
            "select": "DOI,title,container-title,issued,published-print,published-online,author,abstract,URL",
        }
        filters = _year_filter(year_range)
        if filters:
            params["filter"] = filters
        if self.mailto:
            params["mailto"] = self.mailto

        try:
            payload = get_json_with_retries(f"{self.base_url}/works", params=params, timeout=self.timeout)
            items = payload.get("message", {}).get("items", [])
        except httpx.HTTPError as exc:
            raise AdapterError(f"Crossref search failed: {exc}") from exc
        return [_parse_work(item) for item in items]

    def fetch(self, *, doi: str | None = None, title: str | None = None, external_id: str | None = None) -> dict[str, Any] | None:
        if not doi:
            return None
        encoded = quote(normalize_doi(doi), safe="")
        params = {"mailto": self.mailto} if self.mailto else None
        try:
            response = get_response_with_retries(f"{self.base_url}/works/{encoded}", params=params, timeout=self.timeout)
            if response.status_code == 404:
                return None
            response.raise_for_status()
            item = response.json().get("message", {})
        except httpx.HTTPError as exc:
            raise AdapterError(f"Crossref fetch failed: {exc}") from exc
        return _parse_work(item)


def _year_filter(year_range: str | None) -> str:
    if not year_range or "-" not in str(year_range):
        return ""
    start, end = [part.strip() for part in str(year_range).split("-", 1)]
    filters = []
    if start:
        filters.append(f"from-pub-date:{start}-01-01")
    if end:
        filters.append(f"until-pub-date:{end}-12-31")
    return ",".join(filters)


def _year_from_date_parts(item: dict[str, Any]) -> int | None:
    for key in ("published-print", "published-online", "issued"):
        parts = item.get(key, {}).get("date-parts", [])
        if parts and parts[0]:
            try:
                return int(parts[0][0])
            except (TypeError, ValueError):
                continue
    return None


def _authors(item: dict[str, Any]) -> list[str]:
    authors = []
    for author in item.get("author", []) or []:
        given = author.get("given", "")
        family = author.get("family", "")
        name = " ".join(part for part in (given, family) if part).strip()
        if name:
            authors.append(name)
    return authors


def _parse_work(item: dict[str, Any]) -> dict[str, Any]:
    return {
        "title": first_value(item.get("title")) or "",
        "doi": normalize_doi(item.get("DOI")),
        "journal": first_value(item.get("container-title")) or "",
        "year": _year_from_date_parts(item),
        "authors": _authors(item),
        "abstract": clean_abstract(item.get("abstract")),
        "url": item.get("URL") or "",
        "source": "Crossref",
        "external_ids": {"crossref_doi": normalize_doi(item.get("DOI"))} if item.get("DOI") else {},
    }
