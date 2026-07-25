"""Minimal stdio MCP server for materials academic search."""

from __future__ import annotations

import asyncio
import json
import logging
import sys
from pathlib import Path
from typing import Any


if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from academic_search.service import AcademicSearchService
else:
    from .service import AcademicSearchService


SERVER_NAME = "materials-academic-search"
PROTOCOL_VERSION = "2025-06-18"
MAX_STDIN_LINE_BYTES = 1_000_000
logger = logging.getLogger(SERVER_NAME)


TOOL_DEFINITIONS: list[dict[str, Any]] = [
    {
        "name": "list_academic_sources",
        "description": "List enabled and disabled academic metadata sources, including optional API-key gated sources.",
        "inputSchema": {"type": "object", "properties": {}},
    },
    {
        "name": "resolve_paper_ids",
        "description": "Normalize DOI, PMID, PMCID, arXiv, OpenAlex, Semantic Scholar, Scopus EID, and ScienceDirect PII identifiers.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "record": {"type": "object"},
                "doi": {"type": "string"},
                "pmid": {"type": "string"},
                "pmcid": {"type": "string"},
                "arxiv": {"type": "string"},
                "openalex": {"type": "string"},
                "semantic_scholar": {"type": "string"},
                "scopus_eid": {"type": "string"},
                "pii": {"type": "string"},
            },
        },
    },
    {
        "name": "convert_citation_records",
        "description": "Parse RIS, BibTeX, NBIB, or CSV records and export RIS, BibTeX, GB/T 7714, CSL JSON, or JSONL.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "content": {"type": "string"},
                "input_format": {"type": "string", "enum": ["ris", "bibtex", "nbib", "csv"], "default": "ris"},
                "output_format": {"type": "string", "enum": ["ris", "bibtex", "gbt7714", "csl-json", "jsonl"], "default": "csl-json"},
                "deduplicate": {"type": "boolean", "default": True},
            },
            "required": ["content"],
        },
    },
    {
        "name": "deduplicate_citation_records",
        "description": "Deduplicate citation records by DOI, external IDs, then normalized title and year.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "records": {"type": "array", "items": {"type": "object"}},
                "content": {"type": "string"},
                "input_format": {"type": "string", "enum": ["ris", "bibtex", "nbib", "csv"], "default": "ris"},
            },
        },
    },
    {
        "name": "search_materials",
        "description": "Search scholarly sources for materials science and engineering papers with journal and evidence-layer filters.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "topic": {"type": "string"},
                "journal_family": {"oneOf": [{"type": "string"}, {"type": "array", "items": {"type": "string"}}]},
                "material_domain": {"type": "string", "default": "general"},
                "evidence_layer": {"type": "string"},
                "year_range": {"type": "string", "description": "Example: 2020-2026"},
                "limit": {"type": "integer", "default": 10},
            },
            "required": ["topic"],
        },
    },
    {
        "name": "fetch_paper_metadata",
        "description": "Resolve DOI, title, year, journal, author, abstract, and source metadata for one paper.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "doi": {"type": "string"},
                "title": {"type": "string"},
                "external_id": {"type": "string"},
                "openalex_id": {"type": "string"},
                "semantic_scholar_id": {"type": "string"},
            },
        },
    },
    {
        "name": "suggest_search_queries",
        "description": "Generate CBM/CCC/JBE/RMPD/IJPE/JRE/CSCM-aware Boolean search queries.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "topic": {"type": "string"},
                "journal_family": {"oneOf": [{"type": "string"}, {"type": "array", "items": {"type": "string"}}]},
                "material_domain": {"type": "string", "default": "general"},
                "evidence_layer": {"type": "string"},
                "year_range": {"type": "string"},
                "limit": {"type": "integer", "default": 6},
            },
            "required": ["topic"],
        },
    },
    {
        "name": "lookup_mesh",
        "description": "Look up PubMed MeSH terms for a materials or chemistry topic.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "topic": {"type": "string"},
                "limit": {"type": "integer", "default": 10},
            },
            "required": ["topic"],
        },
    },
    {
        "name": "build_claim_source_map",
        "description": "Map manuscript claims to evidence type, search query, candidate sources, and reviewer risk.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "topic": {"type": "string"},
                "claims": {"type": "array", "items": {"type": "string"}},
                "text": {"type": "string"},
                "candidate_records": {"type": "array", "items": {"type": "object"}},
                "journal_family": {"oneOf": [{"type": "string"}, {"type": "array", "items": {"type": "string"}}]},
                "material_domain": {"type": "string", "default": "general"},
                "year_range": {"type": "string"},
            },
        },
    },
    {
        "name": "audit_reference_gaps",
        "description": "Flag missing mechanism, performance, durability, and reviewer-safe source evidence.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "claims": {"type": "array", "items": {"type": "string"}},
                "text": {"type": "string"},
                "claim_source_map": {"type": "array", "items": {"type": "object"}},
                "candidate_records": {"type": "array", "items": {"type": "object"}},
            },
        },
    },
    {
        "name": "export_citation_matrix",
        "description": "Export rows compatible with the materials citation matrix template.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "topic": {"type": "string"},
                "claims": {"type": "array", "items": {"type": "string"}},
                "target_journals": {"oneOf": [{"type": "string"}, {"type": "array", "items": {"type": "string"}}]},
                "journal_family": {"oneOf": [{"type": "string"}, {"type": "array", "items": {"type": "string"}}]},
                "material_domain": {"type": "string", "default": "general"},
                "year_range": {"type": "string"},
                "manuscript_location": {"type": "string"},
            },
        },
    },
    {
        "name": "get_formatted_citation",
        "description": "Generate formatted citation strings or export files for papers by DOI. Supports RIS, BibTeX, GB/T 7714, and APA/Nature/IEEE styles.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "doi": {"type": "string", "description": "Single paper DOI"},
                "dois": {"type": "array", "items": {"type": "string"}, "description": "Multiple DOIs for batch export"},
                "format": {
                    "type": "string",
                    "enum": ["ris", "bibtex", "gbt7714", "csl-json", "jsonl", "apa", "nature", "ieee"],
                    "default": "ris",
                    "description": "Export format. ris/bibtex/gbt7714 are client-side; apa/nature/ieee use CrossRef content negotiation.",
                },
                "records": {"type": "array", "items": {"type": "object"}, "description": "Pre-fetched record dicts (skips DOI lookup)"},
            },
        },
    },
]


def handle_message(message: dict[str, Any], *, service: AcademicSearchService | None = None) -> dict[str, Any] | None:
    """Handle one JSON-RPC message."""

    request_id = message.get("id")
    method = message.get("method")
    if request_id is None and method and method.startswith("notifications/"):
        return None
    service = service or AcademicSearchService()

    try:
        if method == "initialize":
            return _result(
                request_id,
                {
                    "protocolVersion": PROTOCOL_VERSION,
                    "capabilities": {"tools": {}},
                    "serverInfo": {"name": SERVER_NAME, "version": "0.1.0"},
                },
            )
        if method == "tools/list":
            return _result(request_id, {"tools": TOOL_DEFINITIONS})
        if method == "tools/call":
            params = message.get("params") or {}
            payload = _call_tool(service, params.get("name"), params.get("arguments") or {})
            return _result(
                request_id,
                {
                    "content": [{"type": "text", "text": json.dumps(payload, ensure_ascii=False, indent=2)}],
                    "structuredContent": payload,
                },
            )
        return _error(request_id, -32601, f"Unknown method: {method}")
    except MethodNotFound as exc:
        return _error(request_id, -32601, str(exc))
    except ValueError as exc:
        return _error(request_id, -32602, str(exc))
    except Exception as exc:  # MCP clients should get a machine-readable failure.
        logger.exception("MCP request failed")
        return _error(request_id, -32603, str(exc))


def _call_tool(service: AcademicSearchService, name: str | None, args: dict[str, Any]) -> dict[str, Any]:
    if name == "list_academic_sources":
        return service.list_academic_sources(args)
    if name == "resolve_paper_ids":
        return service.resolve_paper_ids(args)
    if name == "convert_citation_records":
        return service.convert_citation_records(args)
    if name == "deduplicate_citation_records":
        return service.deduplicate_citation_records(args)
    if name == "search_materials":
        return _run_async_or_sync(service, "search_materials", "search_materials_async", args)
    if name == "fetch_paper_metadata":
        return _run_async_or_sync(service, "fetch_paper_metadata", "fetch_paper_metadata_async", args)
    if name == "suggest_search_queries":
        return service.suggest_search_queries(args)
    if name == "lookup_mesh":
        return service.lookup_mesh(args)
    if name == "build_claim_source_map":
        return service.build_claim_source_map(args)
    if name == "audit_reference_gaps":
        return service.audit_reference_gaps(args)
    if name == "export_citation_matrix":
        return service.export_citation_matrix(args)
    if name == "get_formatted_citation":
        return service.get_formatted_citation(args)
    raise MethodNotFound(f"Unknown tool: {name}")


class MethodNotFound(ValueError):
    pass


def _run_async_or_sync(
    service: AcademicSearchService,
    sync_name: str,
    async_name: str,
    args: dict[str, Any],
) -> dict[str, Any]:
    """Use async if available and no event loop is running; otherwise fall back to sync."""
    async_fn = getattr(service, async_name, None)
    sync_fn = getattr(service, sync_name, None)

    # Prefer async when available and no loop is already running
    if async_fn is not None:
        try:
            asyncio.get_running_loop()
        except RuntimeError:
            return asyncio.run(async_fn(args))

    # Fall back to sync
    if sync_fn is not None:
        return sync_fn(args)

    raise MethodNotFound(f"Neither {sync_name} nor {async_name} found on service")


def _result(request_id: Any, result: dict[str, Any]) -> dict[str, Any]:
    return {"jsonrpc": "2.0", "id": request_id, "result": result}


def _error(request_id: Any, code: int, message: str) -> dict[str, Any]:
    return {"jsonrpc": "2.0", "id": request_id, "error": {"code": code, "message": message}}


def main() -> int:
    service = AcademicSearchService()
    for line in sys.stdin:
        if not line.strip():
            continue
        if len(line.encode("utf-8")) > MAX_STDIN_LINE_BYTES:
            print(json.dumps(_error(None, -32600, "Request line exceeds 1 MB limit."), ensure_ascii=False), flush=True)
            continue
        try:
            message = json.loads(line)
            response = handle_message(message, service=service)
        except json.JSONDecodeError as exc:
            response = _error(None, -32700, f"Parse error: {exc}")
        if response is not None:
            print(json.dumps(response, ensure_ascii=False), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
