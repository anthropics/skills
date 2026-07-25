"""Service layer for materials academic search tools."""

from __future__ import annotations

import asyncio
import csv
import io
import logging
from collections.abc import Iterable
from typing import Any

from .adapters import (
    AcademicSourceAdapter,
    AdapterDisabled,
    AdapterError,
    ArxivAdapter,
    CrossrefAdapter,
    OpenAlexAdapter,
    PubMedAdapter,
    ScienceDirectAdapter,
    ScopusAdapter,
    SemanticScholarAdapter,
    normalize_doi,
    normalize_title,
)
from .adapters.base import get_response_with_retries
from .export.formats import export_citations
from .importers.citation_files import parse_citation_records
from .domain.classifier import (
    DURABILITY_LAYERS,
    MECHANISM_LAYERS,
    PERFORMANCE_LAYERS,
    canonical_evidence_layer,
    classify_evidence_layers,
    evidence_type_for_claim,
)
from .domain.identifiers import (
    deduplicate_records,
    merge_external_ids,
    normalize_arxiv_id,
    normalize_openalex_id,
    normalize_pii,
    normalize_pmcid,
    normalize_pmid,
    normalize_scopus_eid,
    normalize_semantic_scholar_id,
)
from .domain.journals import expand_journal_terms, normalize_to_list
from .domain.queries import suggest_queries


CSV_FIELDS = [
    "claim_id",
    "priority",
    "claim_or_need",
    "evidence_layer",
    "source_role",
    "source_quality",
    "mechanism_directness",
    "durability_relevance",
    "service_relevance",
    "reader_anchor",
    "figure_handoff",
    "reviewer_risk",
    "search_query",
    "target_journals",
    "evidence_type",
    "candidate_source",
    "status",
    "manuscript_location",
    "risk_note",
]

DEFAULT_CLAIMS = [
    "Research gap and novelty",
    "Material design rationale",
    "Performance improvement",
    "Mechanism explanation",
    "Durability or service-condition relevance",
]

logger = logging.getLogger(__name__)
logger.addHandler(logging.NullHandler())


class AcademicSearchService:
    """High-level operations exposed through the MCP tools."""

    def __init__(self, adapters: list[AcademicSourceAdapter] | None = None) -> None:
        self.adapters = adapters if adapters is not None else [
            CrossrefAdapter(),
            PubMedAdapter(),
            ArxivAdapter(),
            OpenAlexAdapter(),
            SemanticScholarAdapter(),
            *_optional_adapters(),
        ]

    def list_academic_sources(self, args: dict[str, Any] | None = None) -> dict[str, Any]:
        sources = []
        warnings = []
        for adapter in self.adapters:
            sources.append({"name": adapter.name, "enabled": True, "optional": adapter.name in {"scopus", "sciencedirect"}})
        for adapter_cls in (ScopusAdapter, ScienceDirectAdapter):
            if any(isinstance(adapter, adapter_cls) for adapter in self.adapters):
                continue
            try:
                adapter_cls()
            except AdapterDisabled as exc:
                warnings.append(str(exc))
                sources.append({"name": adapter_cls.name, "enabled": False, "optional": True, "warning": str(exc)})
        return {"sources": sources, "warnings": warnings}

    def resolve_paper_ids(self, args: dict[str, Any]) -> dict[str, Any]:
        record = dict(args.get("record") or {})
        if args.get("doi"):
            record["doi"] = args.get("doi")
        external_ids = dict(record.get("external_ids") or {})
        for key, normalizer in (
            ("pmid", normalize_pmid),
            ("pmcid", normalize_pmcid),
            ("arxiv", normalize_arxiv_id),
            ("openalex", normalize_openalex_id),
            ("semantic_scholar", normalize_semantic_scholar_id),
            ("scopus_eid", normalize_scopus_eid),
            ("pii", normalize_pii),
        ):
            value = args.get(key) or args.get(f"{key}_id")
            if value and (normalized := normalizer(value)):
                external_ids[key] = normalized
        record["external_ids"] = external_ids
        ids = merge_external_ids([record])
        return {"external_ids": ids}

    def convert_citation_records(self, args: dict[str, Any]) -> dict[str, Any]:
        content = _required(args, "content")
        input_format = (args.get("input_format") or "ris").lower().strip()
        output_format = (args.get("output_format") or "csl-json").lower().strip()
        records = parse_citation_records(content, input_format)
        records = deduplicate_records(records) if args.get("deduplicate", True) else records
        output = export_citations(records, output_format)
        return {
            "input_format": input_format,
            "output_format": output_format,
            "count": len(records),
            "records": records,
            "content": output,
            "warnings": [],
        }

    def deduplicate_citation_records(self, args: dict[str, Any]) -> dict[str, Any]:
        records = list(args.get("records") or [])
        if args.get("content"):
            records.extend(parse_citation_records(str(args["content"]), args.get("input_format") or "ris"))
        deduplicated = deduplicate_records(records)
        return {"records": deduplicated, "count": len(deduplicated), "input_count": len(records)}

    def search_materials(self, args: dict[str, Any]) -> dict[str, Any]:
        topic = _required(args, "topic")
        limit = _safe_limit(args.get("limit"), default=10)
        journal_family = args.get("journal_family")
        evidence_layer = args.get("evidence_layer")
        year_range = args.get("year_range")
        queries = suggest_queries(
            topic=topic,
            journal_family=journal_family,
            material_domain=args.get("material_domain") or "general",
            evidence_layer=evidence_layer,
            year_range=year_range,
            limit=1,
        )
        query = queries[0]["query"]
        raw_records: list[dict[str, Any]] = []
        warnings: list[str] = []

        for adapter in self.adapters:
            try:
                raw_records.extend(
                    adapter.search(
                        query,
                        journals=expand_journal_terms(journal_family),
                        year_range=year_range,
                        limit=limit,
                    )
                )
            except AdapterDisabled as exc:
                logger.warning("Academic source disabled during search: %s", exc)
                warnings.append(str(exc))
            except AdapterError as exc:
                logger.warning("Academic source failed during search: %s", exc)
                warnings.append(str(exc))

        records = merge_records(raw_records, fallback_evidence_layer=evidence_layer)
        records.sort(key=lambda item: (item.get("confidence", 0), item.get("year") or 0), reverse=True)
        return {
            "query": query,
            "queries": queries,
            "records": records[:limit],
            "warnings": warnings,
            "tool_notes": [
                "Records are candidates, not deep-read evidence.",
                "Do not claim novelty or mechanism until sources are read with materials-reader.",
            ],
        }

    def fetch_paper_metadata(self, args: dict[str, Any]) -> dict[str, Any]:
        doi = normalize_doi(args.get("doi"))
        title = args.get("title")
        external_id = args.get("external_id") or args.get("openalex_id") or args.get("semantic_scholar_id")
        if not any([doi, title, external_id]):
            raise ValueError("doi, title, or external_id is required")

        raw_records: list[dict[str, Any]] = []
        warnings: list[str] = []
        for adapter in self.adapters:
            try:
                record = adapter.fetch(doi=doi, title=title, external_id=external_id)
            except AdapterDisabled as exc:
                logger.warning("Academic source disabled during metadata fetch: %s", exc)
                warnings.append(str(exc))
                continue
            except AdapterError as exc:
                logger.warning("Academic source failed during metadata fetch: %s", exc)
                warnings.append(str(exc))
                continue
            if record:
                raw_records.append(record)

        records = merge_records(raw_records)
        return {
            "record": records[0] if records else _empty_record(doi=doi, title=title),
            "warnings": warnings,
        }

    # ── Async variants for concurrent adapter execution ────────────────

    async def _run_adapter_method(
        self,
        method_name: str,
        *args: Any,
        **kwargs: Any,
    ) -> tuple[list[Any], list[str]]:
        """Run *method_name* on every adapter concurrently via asyncio.to_thread."""

        async def _call_one(adapter: AcademicSourceAdapter) -> Any:
            fn = getattr(adapter, method_name)
            try:
                result = await asyncio.to_thread(fn, *args, **kwargs)
                return ("ok", result)
            except AdapterDisabled as exc:
                return ("warning", str(exc))
            except AdapterError as exc:
                return ("warning", str(exc))

        outcomes = await asyncio.gather(*[_call_one(a) for a in self.adapters])
        records: list[Any] = []
        warnings: list[str] = []
        for status, payload in outcomes:
            if status == "warning":
                warnings.append(payload)  # type: ignore[arg-type]
            elif isinstance(payload, list):
                records.extend(payload)
            elif payload is not None:
                records.append(payload)
        return records, warnings

    async def search_materials_async(self, args: dict[str, Any]) -> dict[str, Any]:
        """Concurrent version of :meth:`search_materials`."""
        topic = _required(args, "topic")
        limit = _safe_limit(args.get("limit"), default=10)
        journal_family = args.get("journal_family")
        evidence_layer = args.get("evidence_layer")
        year_range = args.get("year_range")
        queries = suggest_queries(
            topic=topic,
            journal_family=journal_family,
            material_domain=args.get("material_domain") or "general",
            evidence_layer=evidence_layer,
            year_range=year_range,
            limit=1,
        )
        query = queries[0]["query"]
        journals = expand_journal_terms(journal_family)

        raw_records, warnings = await self._run_adapter_method(
            "search", query, journals=journals, year_range=year_range, limit=limit,
        )

        records = merge_records(raw_records, fallback_evidence_layer=evidence_layer)
        records.sort(key=lambda item: (item.get("confidence", 0), item.get("year") or 0), reverse=True)
        return {
            "query": query,
            "queries": queries,
            "records": records[:limit],
            "warnings": warnings,
            "tool_notes": [
                "Records are candidates, not deep-read evidence.",
                "Do not claim novelty or mechanism until sources are read with materials-reader.",
            ],
        }

    async def fetch_paper_metadata_async(self, args: dict[str, Any]) -> dict[str, Any]:
        """Concurrent version of :meth:`fetch_paper_metadata`."""
        doi = normalize_doi(args.get("doi"))
        title = args.get("title")
        external_id = args.get("external_id") or args.get("openalex_id") or args.get("semantic_scholar_id")
        if not any([doi, title, external_id]):
            raise ValueError("doi, title, or external_id is required")

        raw_records, warnings = await self._run_adapter_method(
            "fetch", doi=doi, title=title, external_id=external_id,
        )

        records = merge_records(raw_records)
        return {
            "record": records[0] if records else _empty_record(doi=doi, title=title),
            "warnings": warnings,
        }

    def suggest_search_queries(self, args: dict[str, Any]) -> dict[str, Any]:
        return {
            "queries": suggest_queries(
                topic=_required(args, "topic"),
                journal_family=args.get("journal_family"),
                material_domain=args.get("material_domain") or "general",
                evidence_layer=args.get("evidence_layer"),
                year_range=args.get("year_range"),
                limit=_safe_limit(args.get("limit"), default=6),
            )
        }

    def lookup_mesh(self, args: dict[str, Any]) -> dict[str, Any]:
        topic = _required(args, "topic")
        limit = _safe_limit(args.get("limit"), default=10, maximum=20)
        warnings: list[str] = []
        for adapter in self.adapters:
            lookup = getattr(adapter, "lookup_mesh", None)
            if not lookup:
                continue
            try:
                return lookup(topic, limit=limit)
            except AdapterDisabled as exc:
                logger.warning("Academic source disabled during MeSH lookup: %s", exc)
                warnings.append(str(exc))
            except AdapterError as exc:
                logger.warning("Academic source failed during MeSH lookup: %s", exc)
                warnings.append(str(exc))
        return {"topic": topic, "mesh_terms": [], "scope_notes": [], "source": "PubMed MeSH", "warnings": warnings}

    def build_claim_source_map(self, args: dict[str, Any]) -> dict[str, Any]:
        topic = args.get("topic") or ""
        claims = _claims_from_args(args)
        candidate_records = args.get("candidate_records") or []
        rows = []

        for claim in claims:
            layers = classify_evidence_layers(claim)
            evidence_type = evidence_type_for_claim(claim)
            matching_records = _matching_records(candidate_records, layers, evidence_type)
            risk_flags = _risk_flags_for_claim(claim, evidence_type, matching_records)
            rows.append(
                {
                    "claim": claim,
                    "evidence_type_needed": evidence_type,
                    "evidence_layers_needed": layers,
                    "candidate_records": matching_records,
                    "search_query": suggest_queries(
                        topic=topic or claim,
                        journal_family=args.get("journal_family"),
                        material_domain=args.get("material_domain") or "general",
                        evidence_layer=layers[0] if layers else None,
                        year_range=args.get("year_range"),
                        limit=1,
                    )[0]["query"],
                    "risk_flags": risk_flags,
                }
            )
        return {"claim_source_map": rows}

    def audit_reference_gaps(self, args: dict[str, Any]) -> dict[str, Any]:
        rows = args.get("claim_source_map")
        if not rows:
            rows = self.build_claim_source_map(args)["claim_source_map"]

        gaps = []
        for row in rows:
            evidence_type = row.get("evidence_type_needed") or evidence_type_for_claim(row.get("claim"))
            records = row.get("candidate_records") or []
            risk_flags = list(row.get("risk_flags") or [])
            if not records:
                risk_flags.append("No confirmed source mapped to this claim.")
            if evidence_type == "mechanism" and not _records_have_layer(records, "microstructure_chemistry"):
                risk_flags.append("Mechanism claim lacks FTIR/SEM/fluorescence/rheology evidence.")
            if evidence_type == "durability" and not _records_have_layer(records, "moisture_aging_durability"):
                risk_flags.append("Durability claim lacks moisture, aging, or service-condition evidence.")
            if risk_flags:
                gaps.append({"claim": row.get("claim"), "evidence_type": evidence_type, "risk_flags": _unique(risk_flags)})
        return {"gaps": gaps}

    def export_citation_matrix(self, args: dict[str, Any]) -> dict[str, Any]:
        topic = args.get("topic") or "[topic]"
        claims = _claims_from_args(args) or DEFAULT_CLAIMS
        journals = expand_journal_terms(args.get("target_journals") or args.get("journal_family"))
        rows = []

        for index, claim in enumerate(claims, 1):
            evidence_type = evidence_type_for_claim(claim)
            evidence_layers = classify_evidence_layers(claim)
            evidence_layer = evidence_layers[0] if evidence_layers else _default_layer_for_evidence_type(evidence_type)
            query = suggest_queries(
                topic=topic,
                journal_family=journals,
                material_domain=args.get("material_domain") or "general",
                evidence_layer=evidence_layer,
                year_range=args.get("year_range"),
                limit=1,
            )[0]["query"]
            rows.append(
                {
                    "claim_id": f"CIT-{index:03d}",
                    "priority": "must-fix" if index <= 2 else "strengthen",
                    "claim_or_need": claim,
                    "evidence_layer": evidence_layer,
                    "source_role": _source_role_for_evidence_type(evidence_type),
                    "source_quality": "screening needed",
                    "mechanism_directness": _mechanism_directness(evidence_type),
                    "durability_relevance": _durability_relevance(evidence_type, evidence_layer),
                    "service_relevance": _service_relevance(evidence_layer),
                    "reader_anchor": args.get("reader_anchor") or "[reader anchor needed]",
                    "figure_handoff": args.get("figure_handoff") or "not assessed",
                    "reviewer_risk": "must-fix" if index <= 2 else "strengthen",
                    "search_query": query,
                    "target_journals": ";".join(journals),
                    "evidence_type": evidence_type,
                    "candidate_source": "[search needed]",
                    "status": "search needed",
                    "manuscript_location": args.get("manuscript_location") or "[assign section]",
                    "risk_note": "Do not make this claim until a confirmed source is mapped.",
                }
            )
        output = io.StringIO()
        writer = csv.DictWriter(output, fieldnames=CSV_FIELDS, lineterminator="\n")
        writer.writeheader()
        csv_rows = [_csv_safe_row(row) for row in rows]
        writer.writerows(csv_rows)
        return {"rows": csv_rows, "csv": output.getvalue()}

    def get_formatted_citation(self, args: dict[str, Any]) -> dict[str, Any]:
        """Generate formatted citation strings or export files."""
        fmt = (args.get("format") or "ris").lower().strip()
        records = list(args.get("records") or [])
        warnings: list[str] = []

        # Collect DOIs
        dois: list[str] = []
        if args.get("doi"):
            dois.append(normalize_doi(args["doi"]))
        if isinstance(args.get("dois"), list):
            dois.extend(normalize_doi(d) for d in args["dois"] if d)
        dois = [d for d in dois if d]

        # If no pre-fetched records, fetch from DOIs
        if not records and dois:
            for doi in dois:
                result = self.fetch_paper_metadata({"doi": doi})
                if result.get("record"):
                    records.append(result["record"])
                warnings.extend(result.get("warnings", []))

        if not records:
            return {"format": fmt, "count": 0, "content": "", "warnings": warnings + ["No records to export."]}

        # Content negotiation for text-based styles (APA, Nature, IEEE)
        if fmt in ("apa", "nature", "ieee"):
            # Collect DOIs from explicit args and from pre-fetched records.
            record_dois = [
                normalize_doi(record.get("doi", ""))
                for record in records
                if record and record.get("doi")
            ]
            doi_pool = [d for d in (dois or record_dois) if d]
            if not doi_pool:
                warnings.append(
                    f"Style '{fmt}' requires DOIs; falling back to structured export."
                )
                content = export_citations(records, fmt)
                return {"format": fmt, "count": len(records), "content": content, "warnings": warnings}
            citations = []
            for doi in doi_pool:
                citation = _crossref_content_negotiation(doi, style=fmt)
                citations.append({"doi": doi, "citation": citation})
            return {"format": fmt, "citations": citations, "warnings": warnings}

        # Client-side export for structured formats
        content = export_citations(records, fmt)
        return {"format": fmt, "count": len(records), "content": content, "warnings": warnings}


def _optional_adapters() -> list[AcademicSourceAdapter]:
    adapters: list[AcademicSourceAdapter] = []
    for adapter_cls in (ScopusAdapter, ScienceDirectAdapter):
        try:
            adapters.append(adapter_cls())
        except AdapterDisabled as exc:
            logger.warning("Optional academic source disabled: %s", exc)
    return adapters


def _crossref_content_negotiation(doi: str, style: str = "apa") -> str:
    """Get a pre-formatted citation from CrossRef content negotiation."""
    url = f"https://api.crossref.org/works/{doi}/transform"
    headers = {"Accept": f"text/x-bibliography; style={style}"}
    try:
        response = get_response_with_retries(url, headers=headers, timeout=15.0)
        if response.status_code == 200:
            return response.text.strip()
        if response.status_code == 404:
            return f"[Citation not available for {doi}]"
        return f"[CrossRef returned status {response.status_code} for {doi}]"
    except Exception:
        return f"[Failed to retrieve citation for {doi}]"


def merge_records(raw_records: Iterable[dict[str, Any]], *, fallback_evidence_layer: str | None = None) -> list[dict[str, Any]]:
    merged: dict[str, dict[str, Any]] = {}
    for raw in raw_records:
        if not raw:
            continue
        record = _normalized_record(raw, fallback_evidence_layer=fallback_evidence_layer)
        key = record["doi"] or normalize_title(record["title"])
        if not key:
            continue
        if key not in merged:
            merged[key] = record
        else:
            _merge_into(merged[key], record)
    return list(merged.values())


def _normalized_record(raw: dict[str, Any], *, fallback_evidence_layer: str | None = None) -> dict[str, Any]:
    title = raw.get("title") or ""
    abstract = raw.get("abstract") or ""
    doi = normalize_doi(raw.get("doi"))
    layers = classify_evidence_layers(" ".join([title, abstract]))
    fallback_layer = canonical_evidence_layer(fallback_evidence_layer)
    if fallback_layer and fallback_layer not in layers:
        layers.append(fallback_layer)
    record = {
        "title": title,
        "doi": doi,
        "journal": raw.get("journal") or "",
        "year": raw.get("year"),
        "authors": raw.get("authors") or [],
        "abstract": abstract,
        "citation_count": raw.get("citation_count"),
        "url": raw.get("url") or "",
        "evidence_layers": layers,
        "source_provenance": [
            {
                "source": raw.get("source") or "unknown",
                "doi": doi,
                "url": raw.get("url") or "",
                "external_ids": raw.get("external_ids") or {},
            }
        ],
        "metadata_conflicts": {},
        "missing_fields": [],
        "risk_flags": [],
    }
    _refresh_quality_fields(record)
    return record


def _merge_into(target: dict[str, Any], source: dict[str, Any]) -> None:
    for field in ("title", "doi", "journal", "year", "abstract", "url", "citation_count"):
        incoming = source.get(field)
        existing = target.get(field)
        if incoming and not existing:
            target[field] = incoming
        elif incoming and existing and incoming != existing and field in {"title", "journal", "year"}:
            values = {str(existing), str(incoming)}
            values.update(target["metadata_conflicts"].get(field, []))
            target["metadata_conflicts"][field] = sorted(values)

    target["authors"] = _unique([*target.get("authors", []), *source.get("authors", [])])
    target["evidence_layers"] = _unique([*target.get("evidence_layers", []), *source.get("evidence_layers", [])])
    target["source_provenance"].extend(source.get("source_provenance", []))
    _refresh_quality_fields(target)


def _refresh_quality_fields(record: dict[str, Any]) -> None:
    required = ("title", "doi", "journal", "year", "abstract")
    record["missing_fields"] = [field for field in required if not record.get(field)]
    risk_flags = []
    if not record.get("doi"):
        risk_flags.append("Missing DOI; verify metadata before citing.")
    if not record.get("evidence_layers"):
        risk_flags.append("No materials evidence layer detected from title/abstract.")
    if record.get("metadata_conflicts"):
        risk_flags.append("Metadata conflict detected across sources; verify before citing.")
    record["risk_flags"] = _unique(risk_flags)
    record["confidence"] = _confidence(record)


def _confidence(record: dict[str, Any]) -> float:
    score = 0.0
    if record.get("doi"):
        score += 0.30
    if record.get("title"):
        score += 0.20
    if record.get("journal"):
        score += 0.15
    if record.get("year"):
        score += 0.10
    if record.get("abstract"):
        score += 0.10
    if record.get("evidence_layers"):
        score += 0.10
    if len(record.get("source_provenance", [])) > 1:
        score += 0.05
    return round(min(score, 1.0), 2)


def _empty_record(*, doi: str = "", title: str | None = None) -> dict[str, Any]:
    record = _normalized_record({"doi": doi, "title": title or "", "source": "none"})
    record["risk_flags"].append("No upstream source returned metadata.")
    record["risk_flags"] = _unique(record["risk_flags"])
    return record


def _required(args: dict[str, Any], key: str) -> str:
    value = args.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{key} is required")
    return value.strip()


def _safe_limit(value: Any, *, default: int, minimum: int = 1, maximum: int = 50) -> int:
    try:
        limit = int(value)
    except (TypeError, ValueError):
        limit = default
    return max(minimum, min(limit, maximum))


def _claims_from_args(args: dict[str, Any]) -> list[str]:
    claims = args.get("claims")
    if isinstance(claims, list):
        return [str(claim).strip(" -\t") for claim in claims if str(claim).strip()]
    text = args.get("claim") or args.get("text") or args.get("manuscript_text") or ""
    if not text:
        return []
    return [line.strip(" -\t") for line in str(text).splitlines() if line.strip(" -\t")]


def _matching_records(records: list[dict[str, Any]], layers: list[str], evidence_type: str) -> list[dict[str, Any]]:
    if not records:
        return []
    matches = []
    canonical_layers = _canonical_layer_set(layers)
    for record in records:
        record_layers = _canonical_layer_set(record.get("evidence_layers") or classify_evidence_layers(record.get("title", "")))
        if canonical_layers & record_layers:
            matches.append(record)
        elif not canonical_layers and evidence_type == _evidence_type_from_layers(record_layers):
            matches.append(record)
    return matches


def _records_have_layer(records: list[dict[str, Any]], layer: str) -> bool:
    canonical = canonical_evidence_layer(layer)
    return any(canonical in _canonical_layer_set(record.get("evidence_layers") or []) for record in records)


def _risk_flags_for_claim(claim: str, evidence_type: str, records: list[dict[str, Any]]) -> list[str]:
    flags = []
    if not records:
        flags.append("No confirmed source mapped to this claim.")
    if evidence_type == "mechanism" and "figure" in claim.lower():
        flags.append("Do not convert figure captions into unsupported mechanism claims.")
    return flags


def _evidence_type_from_layers(layers: set[str]) -> str:
    layers = _canonical_layer_set(layers)
    if layers & MECHANISM_LAYERS:
        return "mechanism"
    if layers & DURABILITY_LAYERS:
        return "durability"
    if layers & PERFORMANCE_LAYERS:
        return "performance"
    if "review_background" in layers:
        return "review/positioning"
    return "primary evidence"


def _canonical_layer_set(layers: Iterable[Any]) -> set[str]:
    return {
        canonical
        for layer in layers
        if (canonical := canonical_evidence_layer(str(layer)))
    }


def _default_layer_for_evidence_type(evidence_type: str) -> str:
    if evidence_type == "mechanism":
        return "microstructure_chemistry"
    if evidence_type == "durability":
        return "moisture_aging_durability"
    if evidence_type == "review/positioning":
        return "review_background"
    if evidence_type == "performance":
        return "bonding_interface_performance"
    return "material_formulation"


def _source_role_for_evidence_type(evidence_type: str) -> str:
    if evidence_type == "review/positioning":
        return "review evidence"
    return "primary experimental evidence"


def _mechanism_directness(evidence_type: str) -> str:
    if evidence_type == "mechanism":
        return "direct mechanism evidence needed"
    return "not a mechanism claim"


def _durability_relevance(evidence_type: str, evidence_layer: str) -> str:
    if evidence_type == "durability" or evidence_layer in DURABILITY_LAYERS:
        return "direct durability evidence needed"
    return "not a durability claim"


def _service_relevance(evidence_layer: str) -> str:
    if evidence_layer == "service_field_relevance":
        return "direct service or field evidence needed"
    return "lab-scale unless field evidence is mapped"


def _csv_safe_row(row: dict[str, Any]) -> dict[str, Any]:
    return {key: _csv_safe(value) for key, value in row.items()}


def _csv_safe(value: Any) -> Any:
    if not isinstance(value, str):
        return value
    if value.startswith(("=", "+", "-", "@")):
        return f"'{value}"
    return value


def _unique(values: Iterable[Any]) -> list[Any]:
    result = []
    seen_hashable = set()
    for value in values:
        try:
            if value in seen_hashable:
                continue
            seen_hashable.add(value)
            result.append(value)
        except TypeError:
            if value not in result:
                result.append(value)
    return result
