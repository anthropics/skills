"""Optional ScienceDirect article metadata adapter."""

from __future__ import annotations

from typing import Any, Callable
from urllib.parse import quote

from .base import normalize_doi
from .elsevier_common import creator_names, elsevier_headers, get_elsevier_json, require_api_key, year_from_cover_date
from ..domain.identifiers import normalize_pii


class ScienceDirectAdapter:
    name = "sciencedirect"
    article_url = "https://api.elsevier.com/content/article"

    def __init__(self, *, timeout: float = 20.0, getter: Callable[..., Any] | None = None) -> None:
        self.timeout = timeout
        self.getter = getter
        self.api_key = require_api_key("ELSEVIER_API_KEY", "ScienceDirect")

    def search(self, query: str, *, journals=None, year_range: str | None = None, limit: int = 10) -> list[dict[str, Any]]:
        return []

    def fetch(
        self,
        *,
        doi: str | None = None,
        title: str | None = None,
        external_id: str | None = None,
        pii: str | None = None,
    ) -> dict[str, Any] | None:
        normalized_pii = normalize_pii(pii or external_id)
        if doi:
            url = f"{self.article_url}/doi/{quote(normalize_doi(doi), safe='')}"
        elif normalized_pii:
            url = f"{self.article_url}/pii/{quote(normalized_pii, safe='')}"
        else:
            return None
        payload = get_elsevier_json(
            "ScienceDirect",
            url,
            headers=elsevier_headers(self.api_key),
            timeout=self.timeout,
            getter=self.getter,
        )
        coredata = (payload.get("full-text-retrieval-response") or {}).get("coredata") or payload.get("coredata") or {}
        return _parse_coredata(coredata)


def _parse_coredata(item: dict[str, Any]) -> dict[str, Any]:
    doi = normalize_doi(item.get("prism:doi"))
    pii = normalize_pii(item.get("pii") or item.get("dc:identifier"))
    return {
        "title": item.get("dc:title") or "",
        "doi": doi,
        "journal": item.get("prism:publicationName") or "",
        "year": year_from_cover_date(item.get("prism:coverDate")),
        "authors": creator_names(item.get("dc:creator")),
        "abstract": item.get("dc:description") or "",
        "url": item.get("prism:url") or (f"https://linkinghub.elsevier.com/retrieve/pii/{pii}" if pii else ""),
        "source": "sciencedirect",
        "external_ids": {key: value for key, value in {"pii": pii, "doi": doi}.items() if value},
    }
