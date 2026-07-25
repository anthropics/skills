"""PubMed E-utilities adapter."""

from __future__ import annotations

import os
import time
import xml.etree.ElementTree as ET
from typing import Any

import httpx

from ..domain.queries import build_pubmed_query
from .base import AdapterError, clean_abstract, get_response_with_retries, normalize_doi


class PubMedAdapter:
    name = "PubMed"
    base_url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils"

    def __init__(
        self,
        *,
        email: str | None = None,
        api_key: str | None = None,
        timeout: float = 20.0,
        sleep: Any = time.sleep,
    ) -> None:
        self.email = (email if email is not None else os.getenv("MATERIALS_CONTACT_EMAIL", "")).strip()
        self.api_key = (api_key if api_key is not None else os.getenv("NCBI_API_KEY", "")).strip()
        self.timeout = timeout
        self.sleep = sleep
        self.rate_limit_seconds = 0.11 if self.api_key else 0.35

    def search(
        self,
        query: str,
        *,
        journals: Any = None,
        year_range: str | None = None,
        limit: int = 10,
    ) -> list[dict[str, Any]]:
        term = build_pubmed_query(query, journals=journals, year_range=year_range)
        search_params = self._params(
            db="pubmed",
            term=term,
            retmode="xml",
            usehistory="y",
            retmax=max(1, min(int(limit), 50)),
        )
        try:
            search_response = self._get("esearch.fcgi", search_params)
            root = ET.fromstring(search_response.text)
            query_key = _text(root, "QueryKey")
            webenv = _text(root, "WebEnv")
            ids = [_element_text(item) for item in root.findall(".//Id") if _element_text(item)]
            if not query_key and not ids:
                return []
            fetch_params = self._params(
                db="pubmed",
                retmode="xml",
                rettype="abstract",
                retmax=max(1, min(int(limit), 50)),
            )
            if query_key and webenv:
                fetch_params["query_key"] = query_key
                fetch_params["WebEnv"] = webenv
            else:
                fetch_params["id"] = ",".join(ids[:limit])
            fetch_response = self._get("efetch.fcgi", fetch_params)
        except (ET.ParseError, httpx.HTTPError) as exc:
            raise AdapterError(f"PubMed search failed: {exc}") from exc
        return _parse_articles(fetch_response.text)

    def fetch(
        self,
        *,
        doi: str | None = None,
        title: str | None = None,
        external_id: str | None = None,
    ) -> dict[str, Any] | None:
        pmid = str(external_id or "").strip()
        if pmid.isdigit():
            records = self._fetch_pmids([pmid])
            return records[0] if records else None
        if doi:
            records = self.search(f"{normalize_doi(doi)}[AID]", limit=1)
            return records[0] if records else None
        if title:
            records = self.search(f'"{title}"[Title]', limit=1)
            return records[0] if records else None
        return None

    def lookup_mesh(self, topic: str, *, limit: int = 10) -> dict[str, Any]:
        topic = str(topic or "").strip()
        if not topic:
            raise ValueError("topic is required")
        safe_limit = max(1, min(int(limit), 20))
        try:
            search_response = self._get(
                "esearch.fcgi",
                self._params(db="mesh", term=topic, retmode="xml", retmax=safe_limit),
            )
            root = ET.fromstring(search_response.text)
            ids = [_element_text(item) for item in root.findall(".//Id") if _element_text(item)]
            if not ids:
                return {"topic": topic, "mesh_terms": [], "scope_notes": [], "source": "PubMed MeSH"}
            summary_response = self._get(
                "esummary.fcgi",
                self._params(db="mesh", id=",".join(ids[:safe_limit]), retmode="xml"),
            )
            return _parse_mesh_summary(topic, summary_response.text)
        except (ET.ParseError, httpx.HTTPError) as exc:
            raise AdapterError(f"PubMed MeSH lookup failed: {exc}") from exc

    def _fetch_pmids(self, pmids: list[str]) -> list[dict[str, Any]]:
        try:
            response = self._get(
                "efetch.fcgi",
                self._params(db="pubmed", id=",".join(pmids), retmode="xml", rettype="abstract"),
            )
        except httpx.HTTPError as exc:
            raise AdapterError(f"PubMed fetch failed: {exc}") from exc
        return _parse_articles(response.text)

    def _get(self, endpoint: str, params: dict[str, Any]) -> Any:
        self.sleep(self.rate_limit_seconds)
        response = get_response_with_retries(f"{self.base_url}/{endpoint}", params=params, timeout=self.timeout)
        response.raise_for_status()
        return response

    def _params(self, **params: Any) -> dict[str, Any]:
        merged = {"tool": "materials-academic-search", **params}
        if self.email:
            merged["email"] = self.email
        if self.api_key:
            merged["api_key"] = self.api_key
        return merged


def _parse_articles(xml_text: str) -> list[dict[str, Any]]:
    root = ET.fromstring(xml_text)
    return [_parse_article(article) for article in root.findall(".//PubmedArticle")]


def _parse_article(element: ET.Element) -> dict[str, Any]:
    article = element.find(".//Article")
    medline = element.find(".//MedlineCitation")
    pmid = _text(medline, "PMID")
    title = _text(article, "ArticleTitle")
    abstract = _abstract(article)
    doi = _doi(article)
    return {
        "title": title,
        "authors": _authors(article),
        "year": _year(article),
        "doi": doi,
        "pmid": pmid,
        "journal": _journal(article),
        "abstract": abstract,
        "url": f"https://pubmed.ncbi.nlm.nih.gov/{pmid}/" if pmid else "",
        "source": "PubMed",
        "external_ids": {"pmid": pmid} if pmid else {},
        "source_provenance": [{"source": "PubMed", "pmid": pmid, "doi": doi}],
    }


def _abstract(article: ET.Element | None) -> str:
    if article is None:
        return ""
    parts = []
    for abstract_text in article.findall(".//AbstractText"):
        text = clean_abstract(_element_text(abstract_text))
        if not text:
            continue
        label = abstract_text.get("Label", "").strip()
        parts.append(f"{label}: {text}" if label else text)
    return " ".join(parts)


def _authors(article: ET.Element | None) -> list[str]:
    if article is None:
        return []
    authors = []
    for author in article.findall(".//Author"):
        collective = _text(author, "CollectiveName")
        if collective:
            authors.append(collective)
            continue
        last = _text(author, "LastName")
        fore = _text(author, "ForeName")
        initials = _text(author, "Initials")
        given = fore or initials
        name = " ".join(part for part in (given, last) if part).strip()
        if name:
            authors.append(name)
    return authors


def _journal(article: ET.Element | None) -> str:
    return _text(article, ".//Journal/Title") or _text(article, ".//Journal/ISOAbbreviation")


def _year(article: ET.Element | None) -> int | None:
    candidates = [
        _text(article, ".//ArticleDate/Year"),
        _text(article, ".//PubDate/Year"),
        _text(article, ".//PubDate/MedlineDate"),
    ]
    for candidate in candidates:
        if candidate and candidate[:4].isdigit():
            return int(candidate[:4])
    return None


def _doi(article: ET.Element | None) -> str:
    if article is None:
        return ""
    for eid in article.findall(".//ELocationID"):
        if eid.get("EIdType", "").lower() == "doi":
            return normalize_doi(_element_text(eid))
    for article_id in article.findall(".//ArticleId"):
        if article_id.get("IdType", "").lower() == "doi":
            return normalize_doi(_element_text(article_id))
    return ""


def _parse_mesh_summary(topic: str, xml_text: str) -> dict[str, Any]:
    root = ET.fromstring(xml_text)
    terms: list[str] = []
    scope_notes: list[str] = []
    for summary in root.findall(".//DocumentSummary"):
        for term in summary.findall(".//DS_MeshTerms/string"):
            value = _element_text(term)
            if value and value not in terms:
                terms.append(value)
        for note in summary.findall(".//ScopeNote"):
            value = _element_text(note)
            if value and value not in scope_notes:
                scope_notes.append(value)
    return {"topic": topic, "mesh_terms": terms, "scope_notes": scope_notes, "source": "PubMed MeSH"}


def _text(element: ET.Element | None, path: str) -> str:
    if element is None:
        return ""
    found = element.find(path)
    return _element_text(found)


def _element_text(element: ET.Element | None) -> str:
    if element is None:
        return ""
    return " ".join("".join(element.itertext()).split())
