#!/usr/bin/env python3
"""Company Research v2 -- structured data collector via ToolUniverse SDK.

Outputs JSON (not markdown). Claude Code consumes this JSON and layers on
MCP tools + analytical reasoning to produce the final intelligence brief.
"""

from __future__ import annotations

import json
import logging
import re
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any

from tooluniverse import ToolUniverse

log = logging.getLogger(__name__)


def company_research(
    company_name: str,
    output_dir: str | None = None,
) -> str:
    """Collect structured intelligence data for a company.

    Returns path to the generated JSON artifact.
    """
    tu = ToolUniverse()
    tu.load_tools()

    out = Path(output_dir) if output_dir else Path(".")
    out.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    slug = re.sub(r"[^a-z0-9]+", "_", company_name.lower())[:30]
    json_path = out / f"company_data_{slug}_{ts}.json"

    sources: list[dict[str, Any]] = []
    gaps: list[str] = []

    identity = _disambiguate(tu, company_name, sources)
    is_public = bool(identity.get("cik"))

    results = _collect_parallel(tu, company_name, identity, sources, gaps)

    artifact: dict[str, Any] = {
        "meta": {
            "company": company_name,
            "timestamp": datetime.now().isoformat(),
            "is_public": is_public,
            "version": "2.0",
        },
        "identity": identity,
        "financials": results.get("financials", {}),
        "pipeline": results.get("pipeline", {}),
        "regulatory": results.get("regulatory", {}),
        "foundation": results.get("foundation", {}),
        "sources": sources,
        "data_gaps": gaps,
    }

    json_path.write_text(json.dumps(artifact, indent=2, default=str))
    print(f"Data collected: {json_path} ({json_path.stat().st_size} bytes)")
    return str(json_path)


# ======================================================================
# Phase 0: Disambiguation
# ======================================================================


def _disambiguate(
    tu: ToolUniverse,
    name: str,
    sources: list[dict[str, Any]],
) -> dict[str, Any]:
    """Resolve company identity: name, ticker, CIK, sector."""
    identity: dict[str, Any] = {"name": name, "is_public": False}

    _wiki_identity(tu, name, identity, sources)
    _sec_identity(tu, name, identity, sources)
    _wikidata_identity(tu, name, identity, sources)

    identity["is_public"] = bool(identity.get("cik"))
    return identity


def _wiki_identity(
    tu: ToolUniverse,
    name: str,
    identity: dict[str, Any],
    sources: list[dict[str, Any]],
) -> None:
    try:
        result = tu.tools.Wikipedia_search(
            query=f"{name} company biotechnology", limit=3
        )
        if isinstance(result, dict):
            hits = result.get("results", [])
            if hits:
                identity["name"] = hits[0].get("title", name)
                _log_source(sources, "Wikipedia_search", name, len(hits), "T3")
    except Exception:
        log.debug("Wikipedia search failed", exc_info=True)


def _sec_identity(
    tu: ToolUniverse,
    name: str,
    identity: dict[str, Any],
    sources: list[dict[str, Any]],
) -> None:
    try:
        result = tu.tools.SEC_EDGAR_search_filings(query=name, forms="10-K")
        data = _extract_data(result)
        if isinstance(data, list) and data:
            identity["cik"] = data[0].get("cik", "")
            co = data[0].get("company", "")
            if "(" in co:
                identity["ticker"] = co.split("(")[1].split(")")[0]
            _log_source(sources, "SEC_EDGAR_search_filings", name, len(data), "T1")
    except Exception:
        log.debug("SEC identity lookup failed", exc_info=True)


def _wikidata_identity(
    tu: ToolUniverse,
    name: str,
    identity: dict[str, Any],
    sources: list[dict[str, Any]],
) -> None:
    try:
        result = tu.tools.Wikidata_search_entities(search=name, limit=3)
        if isinstance(result, dict):
            entities = result.get("results", result.get("search", []))
            if isinstance(entities, list) and entities:
                desc = entities[0].get("description", "")
                if desc:
                    identity.setdefault("sector", desc)
                identity["wikidata_id"] = entities[0].get("id", "")
                _log_source(
                    sources, "Wikidata_search_entities", name, len(entities), "T3"
                )
    except Exception:
        log.debug("Wikidata lookup failed", exc_info=True)


# ======================================================================
# Parallel Data Collection (Phases 1-3)
# ======================================================================


def _collect_parallel(
    tu: ToolUniverse,
    name: str,
    identity: dict[str, Any],
    sources: list[dict[str, Any]],
    gaps: list[str],
) -> dict[str, Any]:
    """Run all data collection phases concurrently."""
    tasks = {
        "financials": lambda: _financials(tu, name, identity, sources, gaps),
        "pipeline": lambda: _pipeline(tu, name, sources, gaps),
        "regulatory": lambda: _regulatory(tu, name, sources, gaps),
        "foundation": lambda: _foundation(tu, name, identity, sources, gaps),
    }
    results: dict[str, Any] = {}
    with ThreadPoolExecutor(max_workers=4) as pool:
        futures = {pool.submit(fn): key for key, fn in tasks.items()}
        for future in as_completed(futures):
            key = futures[future]
            try:
                results[key] = future.result()
            except Exception as exc:
                log.warning("Phase %s failed: %s", key, exc)
                results[key] = {}
                gaps.append(f"Phase '{key}' failed: {exc}")
    return results


# ======================================================================
# Phase 1: Financial Intelligence
# ======================================================================


def _financials(
    tu: ToolUniverse,
    name: str,
    identity: dict[str, Any],
    sources: list[dict[str, Any]],
    gaps: list[str],
) -> dict[str, Any]:
    data: dict[str, Any] = {
        "recent_filings": [],
        "full_submissions": {},
    }
    cik = identity.get("cik")
    if not cik:
        gaps.append("No CIK found — skipping SEC financial data (private company)")
        return data

    data["recent_filings"] = _fetch_recent_filings(tu, name, sources, gaps)
    data["full_submissions"] = _fetch_submissions(tu, cik, sources, gaps)
    return data


def _fetch_recent_filings(
    tu: ToolUniverse,
    name: str,
    sources: list[dict[str, Any]],
    gaps: list[str],
) -> list[dict[str, Any]]:
    try:
        cutoff = (datetime.now() - timedelta(days=180)).strftime("%Y-%m-%d")
        result = tu.tools.SEC_EDGAR_search_filings(query=name, startdt=cutoff)
        filings = _extract_list(result)
        seen: set[str] = set()
        deduped = []
        for f in filings[:20]:
            key = f"{f.get('form')}-{f.get('accession')}"
            if key not in seen:
                seen.add(key)
                deduped.append(f)
        _log_source(
            sources, "SEC_EDGAR_search_filings", f"{name} recent", len(deduped), "T1"
        )
        return deduped
    except Exception:
        log.debug("SEC recent filings failed", exc_info=True)
        gaps.append("SEC recent filings search failed")
        return []


def _fetch_submissions(
    tu: ToolUniverse,
    cik: str,
    sources: list[dict[str, Any]],
    gaps: list[str],
) -> dict[str, Any]:
    try:
        padded = cik.zfill(10)
        result = tu.tools.SEC_EDGAR_get_company_submissions(cik=padded)
        data = _extract_data(result)
        if isinstance(data, dict):
            _log_source(sources, "SEC_EDGAR_get_company_submissions", padded, 1, "T1")
            return data
        return {}
    except Exception:
        log.debug("SEC submissions lookup failed", exc_info=True)
        gaps.append("SEC company submissions lookup failed")
        return {}


# ======================================================================
# Phase 2: Pipeline & Science
# ======================================================================


def _pipeline(
    tu: ToolUniverse,
    name: str,
    sources: list[dict[str, Any]],
    gaps: list[str],
) -> dict[str, Any]:
    """Collect pipeline data — sub-tasks run in parallel."""
    sub_tasks = {
        "clinical_trials": lambda: _fetch_trials(tu, name, sources, gaps),
        "preprints": lambda: _fetch_preprints(tu, name, sources, gaps),
        "publications": lambda: _fetch_publications(tu, name, sources, gaps),
        "fda_approved": lambda: _fetch_fda_products(tu, name, sources, gaps),
        "fda_approvals_history": lambda: _fetch_fda_approvals(tu, name, sources, gaps),
        "adverse_events": lambda: _fetch_faers(tu, name, sources, gaps),
        "research_output": lambda: _fetch_openalex(tu, name, sources, gaps),
    }
    results: dict[str, Any] = {}
    with ThreadPoolExecutor(max_workers=5) as pool:
        futures = {pool.submit(fn): key for key, fn in sub_tasks.items()}
        for future in as_completed(futures):
            key = futures[future]
            try:
                results[key] = future.result()
            except Exception:
                log.debug("Pipeline sub-task %s failed", key, exc_info=True)
                results[key] = []
    return results


def _fetch_trials(
    tu: ToolUniverse, name: str, sources: list, gaps: list
) -> list[dict[str, Any]]:
    try:
        result = tu.tools.ClinicalTrials_search_studies(query_term=name, page_size=15)
        studies = _extract_list(result)
        _log_source(sources, "ClinicalTrials_search_studies", name, len(studies), "T1")
        return studies[:15]
    except Exception:
        log.debug("Clinical trials search failed", exc_info=True)
        gaps.append("Clinical trials search failed")
        return []


def _fetch_preprints(
    tu: ToolUniverse, name: str, sources: list, gaps: list
) -> list[dict[str, Any]]:
    try:
        result = tu.tools.EuropePMC_search_articles(query=f"{name} SRC:PPR", limit=8)
        articles = _extract_list(result)
        _log_source(
            sources, "EuropePMC_search_articles", f"{name} SRC:PPR", len(articles), "T3"
        )
        return articles[:8]
    except Exception:
        log.debug("Preprint search failed", exc_info=True)
        gaps.append("Preprint search failed")
        return []


def _fetch_publications(
    tu: ToolUniverse, name: str, sources: list, gaps: list
) -> list[dict[str, Any]]:
    try:
        result = tu.tools.PubMed_search_articles(query=name, limit=8, sort="pub_date")
        articles = _extract_list(result)
        _log_source(sources, "PubMed_search_articles", name, len(articles), "T2")
        return articles[:8]
    except Exception:
        log.debug("PubMed search failed", exc_info=True)
        gaps.append("PubMed search failed")
        return []


def _fetch_fda_products(
    tu: ToolUniverse, name: str, sources: list, gaps: list
) -> list[dict[str, Any]]:
    try:
        result = tu.tools.FDA_OrangeBook_search_drug(brand_name=name, limit=10)
        products = _extract_list(result)
        _log_source(sources, "FDA_OrangeBook_search_drug", name, len(products), "T1")
        return products[:10]
    except Exception:
        log.debug("FDA Orange Book search failed", exc_info=True)
        gaps.append("FDA Orange Book search failed")
        return []


def _fetch_fda_approvals(
    tu: ToolUniverse, name: str, sources: list, gaps: list
) -> list[dict[str, Any]]:
    try:
        result = tu.tools.OpenFDA_search_drug_approvals(
            search=f'sponsor_name:"{name}"', limit=10
        )
        approvals = _extract_list(result)
        _log_source(
            sources, "OpenFDA_search_drug_approvals", name, len(approvals), "T1"
        )
        return approvals[:10]
    except Exception:
        log.debug("OpenFDA drug approvals search failed", exc_info=True)
        gaps.append("OpenFDA drug approvals search failed")
        return []


def _fetch_faers(
    tu: ToolUniverse, name: str, sources: list, gaps: list
) -> list[dict[str, Any]]:
    try:
        result = tu.tools.FAERS_count_reactions_by_drug_event(medicinalproduct=name)
        data = _extract_data(result)
        items = _as_list(data)
        _log_source(
            sources, "FAERS_count_reactions_by_drug_event", name, len(items), "T1"
        )
        return items[:20]
    except Exception:
        log.debug("FAERS adverse event search failed", exc_info=True)
        gaps.append("FAERS adverse event search failed")
        return []


def _fetch_openalex(
    tu: ToolUniverse, name: str, sources: list, gaps: list
) -> list[dict[str, Any]]:
    try:
        result = tu.tools.openalex_literature_search(
            search_keywords=name, max_results=8
        )
        papers = _extract_list(result)
        _log_source(sources, "openalex_literature_search", name, len(papers), "T2")
        return papers[:8]
    except Exception:
        log.debug("OpenAlex search failed", exc_info=True)
        gaps.append("OpenAlex search failed")
        return []


# ======================================================================
# Phase 3: Regulatory Intelligence
# ======================================================================


def _regulatory(
    tu: ToolUniverse,
    name: str,
    sources: list[dict[str, Any]],
    gaps: list[str],
) -> dict[str, Any]:
    return {
        "device_510k": _fetch_510k(tu, name, sources, gaps),
        "enforcement_actions": _fetch_enforcement(tu, name, sources, gaps),
        "drug_labels": _fetch_drug_labels(tu, name, sources, gaps),
    }


def _fetch_510k(
    tu: ToolUniverse, name: str, sources: list, gaps: list
) -> list[dict[str, Any]]:
    try:
        result = tu.tools.OpenFDA_search_device_510k(
            search=f'applicant:"{name}"', limit=10
        )
        items = _extract_list(result)
        _log_source(sources, "OpenFDA_search_device_510k", name, len(items), "T1")
        return items[:10]
    except Exception:
        log.debug("OpenFDA 510(k) search failed", exc_info=True)
        gaps.append("OpenFDA 510(k) device search failed")
        return []


def _fetch_enforcement(
    tu: ToolUniverse, name: str, sources: list, gaps: list
) -> list[dict[str, Any]]:
    try:
        result = tu.tools.OpenFDA_search_drug_enforcement(
            search=f'recalling_firm:"{name}"', limit=10
        )
        items = _extract_list(result)
        _log_source(sources, "OpenFDA_search_drug_enforcement", name, len(items), "T1")
        return items[:10]
    except Exception:
        log.debug("OpenFDA enforcement search failed", exc_info=True)
        gaps.append("OpenFDA enforcement search failed")
        return []


def _fetch_drug_labels(
    tu: ToolUniverse, name: str, sources: list, gaps: list
) -> list[dict[str, Any]]:
    try:
        result = tu.tools.OpenFDA_search_drug_labels(
            search=f'openfda.manufacturer_name:"{name}"', limit=10
        )
        items = _extract_list(result)
        _log_source(sources, "OpenFDA_search_drug_labels", name, len(items), "T1")
        return items[:10]
    except Exception:
        log.debug("OpenFDA drug labels search failed", exc_info=True)
        gaps.append("OpenFDA drug labels search failed")
        return []


# ======================================================================
# Phase 4: Foundation
# ======================================================================


def _foundation(
    tu: ToolUniverse,
    name: str,
    identity: dict[str, Any],
    sources: list[dict[str, Any]],
    gaps: list[str],
) -> dict[str, Any]:
    return {
        "wikipedia_summary": _fetch_wiki_profile(tu, identity, sources, gaps),
        "crossref_works": _fetch_crossref(tu, name, sources, gaps),
    }


def _fetch_wiki_profile(
    tu: ToolUniverse,
    identity: dict[str, Any],
    sources: list,
    gaps: list,
) -> str:
    title = identity.get("name", "")
    try:
        result = tu.tools.Wikipedia_get_content(
            title=title, extract_type="summary", max_chars=4000
        )
        if isinstance(result, dict) and result.get("content"):
            _log_source(sources, "Wikipedia_get_content", title, 1, "T3")
            return result["content"]
        if isinstance(result, str) and len(result) > 50:
            return result[:4000]
    except Exception:
        log.debug("Wikipedia content fetch failed", exc_info=True)
        gaps.append("Wikipedia content fetch failed")
    return ""


def _fetch_crossref(
    tu: ToolUniverse, name: str, sources: list, gaps: list
) -> list[dict[str, Any]]:
    try:
        result = tu.tools.Crossref_search_works(query=name, limit=5)
        works = _extract_list(result)
        _log_source(sources, "Crossref_search_works", name, len(works), "T2")
        return works[:5]
    except Exception:
        log.debug("Crossref search failed", exc_info=True)
        gaps.append("Crossref search failed")
        return []


# ======================================================================
# Helpers
# ======================================================================


def _extract_data(result: object) -> object:
    """Unwrap ToolUniverse response — up to 3 nesting levels."""
    cur = result
    for _ in range(3):
        if not isinstance(cur, dict):
            break
        if cur.get("status") == "success" and "data" in cur:
            cur = cur["data"]
        elif "data" in cur and isinstance(cur["data"], (dict, list)):
            cur = cur["data"]
        else:
            break
    return cur


def _extract_list(result: object) -> list[dict[str, Any]]:
    """Extract data and coerce to list."""
    return _as_list(_extract_data(result))


def _as_list(data: object) -> list[dict[str, Any]]:
    """Coerce response data to a list of dicts."""
    if isinstance(data, list):
        return data
    if isinstance(data, dict):
        for key in ("studies", "results", "items", "articles", "data", "works"):
            if isinstance(data.get(key), list):
                return data[key]
        return [data] if data else []
    return []


def _log_source(
    sources: list[dict[str, Any]],
    tool: str,
    query: str,
    items: int,
    tier: str,
) -> None:
    """Record a data source for provenance tracking."""
    sources.append({"tool": tool, "query": query, "items": items, "tier": tier})


# ======================================================================
# CLI
# ======================================================================

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Company Research v2 data collector")
    parser.add_argument("company", help="Company name")
    parser.add_argument("--output-dir", "-o", default=".", help="Output directory")
    args = parser.parse_args()
    company_research(args.company, args.output_dir)
