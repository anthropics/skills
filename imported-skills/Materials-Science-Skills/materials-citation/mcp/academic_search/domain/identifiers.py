"""Identifier normalization and citation-record deduplication."""

from __future__ import annotations

import re
from collections.abc import Iterable
from typing import Any


_ID_ALIASES = {
    "doi": "doi",
    "crossref_doi": "doi",
    "pmid": "pmid",
    "pubmed": "pmid",
    "pmcid": "pmcid",
    "arxiv": "arxiv",
    "arxiv_id": "arxiv",
    "openalex": "openalex",
    "openalex_id": "openalex",
    "semantic_scholar": "semantic_scholar",
    "semanticscholar": "semantic_scholar",
    "semantic_scholar_id": "semantic_scholar",
    "paperid": "semantic_scholar",
    "paper_id": "semantic_scholar",
    "scopus": "scopus_eid",
    "scopuseid": "scopus_eid",
    "scopus_eid": "scopus_eid",
    "eid": "scopus_eid",
    "pii": "pii",
}


def normalize_doi(value: str | None) -> str | None:
    if not value:
        return None
    doi = str(value).strip()
    doi = re.sub(r"^https?://(dx\.)?doi\.org/", "", doi, flags=re.IGNORECASE)
    doi = re.sub(r"^doi:\s*", "", doi, flags=re.IGNORECASE)
    doi = doi.strip().strip(".")
    return doi.lower() or None


def normalize_pmid(value: str | None) -> str | None:
    if not value:
        return None
    match = re.search(r"\d+", str(value))
    return match.group(0) if match else None


def normalize_pmcid(value: str | None) -> str | None:
    if not value:
        return None
    match = re.search(r"PMC\s*\d+", str(value), flags=re.IGNORECASE)
    if not match:
        digits = re.search(r"\d+", str(value))
        return f"PMC{digits.group(0)}" if digits else None
    return re.sub(r"\s+", "", match.group(0).upper())


def normalize_arxiv_id(value: str | None) -> str | None:
    if not value:
        return None
    text = str(value).strip()
    text = re.sub(r"^https?://arxiv\.org/(abs|pdf)/", "", text, flags=re.IGNORECASE)
    text = re.sub(r"\.pdf$", "", text, flags=re.IGNORECASE)
    text = re.sub(r"^arxiv:\s*", "", text, flags=re.IGNORECASE)
    match = re.search(r"([a-z.-]+/\d{7}(?:v\d+)?|\d{4}\.\d{4,5}(?:v\d+)?)", text, flags=re.IGNORECASE)
    return match.group(1) if match else None


def canonical_arxiv_id(value: str | None) -> str | None:
    arxiv_id = normalize_arxiv_id(value)
    if not arxiv_id:
        return None
    return re.sub(r"v\d+$", "", arxiv_id)


def normalize_openalex_id(value: str | None) -> str | None:
    if not value:
        return None
    text = str(value).strip()
    text = re.sub(r"^https?://openalex\.org/", "", text, flags=re.IGNORECASE)
    return text or None


def normalize_semantic_scholar_id(value: str | None) -> str | None:
    if not value:
        return None
    text = str(value).strip()
    text = re.sub(r"^(semantic[-_ ]?scholar|paperid):\s*", "", text, flags=re.IGNORECASE)
    text = re.sub(r"^https?://www\.semanticscholar\.org/paper/[^/]+/", "", text, flags=re.IGNORECASE)
    return text or None


def normalize_scopus_eid(value: str | None) -> str | None:
    if not value:
        return None
    text = str(value).strip()
    text = re.sub(r"^(eid|scopus_eid):\s*", "", text, flags=re.IGNORECASE)
    return text or None


def normalize_pii(value: str | None) -> str | None:
    if not value:
        return None
    text = str(value).strip()
    text = re.sub(r"^pii:\s*", "", text, flags=re.IGNORECASE)
    text = re.sub(r"^https?://linkinghub\.elsevier\.com/retrieve/pii/", "", text, flags=re.IGNORECASE)
    return text or None


def normalize_title(value: str | None) -> str:
    if not value:
        return ""
    text = re.sub(r"<[^>]+>", " ", str(value))
    text = re.sub(r"[^a-zA-Z0-9]+", " ", text.lower())
    return " ".join(text.split())


def merge_external_ids(records: list[dict[str, Any]]) -> dict[str, str]:
    merged: dict[str, str] = {}
    for record in records:
        candidates: dict[str, Any] = {}
        candidates.update(record.get("external_ids") or {})
        for key in ("doi", "pmid", "pmcid", "arxiv", "openalex", "semantic_scholar", "scopus_eid", "pii"):
            if record.get(key):
                candidates[key] = record.get(key)
        for raw_key, raw_value in candidates.items():
            key = _ID_ALIASES.get(_identifier_key(raw_key))
            value = _normalize_identifier_value(key, raw_value) if key else None
            if key and value and key not in merged:
                merged[key] = value
    return merged


def deduplicate_records(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    groups: list[dict[str, Any]] = []
    for record in records:
        normalized = _copy_record(record)
        normalized["doi"] = normalize_doi(normalized.get("doi")) or ""
        normalized["external_ids"] = merge_external_ids([normalized])
        key = _record_key(normalized)
        for existing in groups:
            if _keys_match(key, existing["_dedup_keys"]):
                _merge_record(existing, normalized)
                break
        else:
            normalized["_dedup_keys"] = key
            normalized["sources"] = _record_sources(normalized)
            groups.append(normalized)
    for record in groups:
        record.pop("_dedup_keys", None)
    return groups


def _identifier_key(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(value).strip().lower()).strip("_")


def _normalize_identifier_value(key: str | None, value: Any) -> str | None:
    if not key or value in {None, ""}:
        return None
    text = str(value)
    if key == "doi":
        return normalize_doi(text)
    if key == "pmid":
        return normalize_pmid(text)
    if key == "pmcid":
        return normalize_pmcid(text)
    if key == "arxiv":
        return normalize_arxiv_id(text)
    if key == "openalex":
        return normalize_openalex_id(text)
    if key == "semantic_scholar":
        return normalize_semantic_scholar_id(text)
    if key == "scopus_eid":
        return normalize_scopus_eid(text)
    if key == "pii":
        return normalize_pii(text)
    return text.strip() or None


def _record_key(record: dict[str, Any]) -> dict[str, set[str]]:
    ids = record.get("external_ids") or {}
    keys: dict[str, set[str]] = {"ids": set(), "title_year": set()}
    for key, value in ids.items():
        if value:
            keys["ids"].add(f"{key}:{value}")
    if record.get("doi"):
        keys["ids"].add(f"doi:{record['doi']}")
    title = normalize_title(record.get("title"))
    year = _year(record.get("year"))
    if title and year:
        keys["title_year"].add(f"{title}|{year}")
    return keys


def _keys_match(key: dict[str, set[str]], existing: dict[str, set[str]]) -> bool:
    return bool(key["ids"] & existing["ids"] or key["title_year"] & existing["title_year"])


def _copy_record(record: dict[str, Any]) -> dict[str, Any]:
    copied = dict(record)
    if isinstance(record.get("authors"), tuple):
        copied["authors"] = list(record["authors"])
    return copied


def _merge_record(target: dict[str, Any], source: dict[str, Any]) -> None:
    for field in ("title", "doi", "journal", "year", "abstract", "url", "citation_count", "volume", "issue", "pages"):
        if source.get(field) and not target.get(field):
            target[field] = source[field]
    target["authors"] = _unique([*(target.get("authors") or []), *(source.get("authors") or [])])
    target["external_ids"] = merge_external_ids([target, source])
    target["sources"] = _unique([*target.get("sources", []), *_record_sources(source)])
    target["_dedup_keys"]["ids"].update(_record_key(source)["ids"])
    target["_dedup_keys"]["title_year"].update(_record_key(source)["title_year"])
    target.setdefault("source_provenance", [])
    if source.get("source_provenance"):
        target["source_provenance"].extend(source["source_provenance"])


def _record_sources(record: dict[str, Any]) -> list[str]:
    values = []
    if record.get("source"):
        values.append(str(record["source"]))
    for item in record.get("source_provenance") or []:
        if isinstance(item, dict) and item.get("source"):
            values.append(str(item["source"]))
    return _unique(values)


def _year(value: Any) -> str:
    match = re.search(r"\d{4}", str(value or ""))
    return match.group(0) if match else ""


def _unique(values: Iterable[Any]) -> list[Any]:
    result = []
    for value in values:
        if value not in result:
            result.append(value)
    return result
