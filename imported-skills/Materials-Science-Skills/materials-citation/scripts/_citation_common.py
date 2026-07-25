"""Shared constants and helpers for materials-citation scripts.

This module is the single source of truth for evidence-layer classification,
journal expansion, and CSV row construction used by both
``build_citation_matrix.py`` and ``citation_search_fallback.py``.

It depends only on the Python standard library (no MCP dependency).
"""

from __future__ import annotations

import re
from pathlib import Path


# ---------------------------------------------------------------------------
# Evidence-layer classification
# ---------------------------------------------------------------------------

EVIDENCE_LAYER_KEYWORDS: dict[str, tuple[str, ...]] = {
    "material_formulation": (
        "waterborne epoxy", "epoxy resin", "epoxy dosage", "resin dosage",
        "formulation", "modifier content", "emulsifier", "mix design", "material design",
    ),
    "emulsion_stability": (
        "emulsion stability", "storage stability", "zeta potential", "particle size",
        "settlement", "segregation", "sieve residue", "stability test",
    ),
    "bonding_interface_performance": (
        "bonding", "bond strength", "pull-off", "interface", "interlayer",
        "adhesion", "adhesive", "tack coat", "shear strength", "direct tension",
    ),
    "rheology": (
        "rheology", "rheological property", "viscosity", "brookfield",
        "flow curve", "shear rate", "dsr", "dynamic shear rheometer",
    ),
    "curing_demulsification": (
        "demulsification", "demulsify", "breaking behavior", "breaking rate",
        "emulsion breaking", "epoxy curing", "curing reaction", "crosslink",
        "cross-link", "amine", "epoxy network", "gel time", "phase compatibility",
    ),
    "microstructure_chemistry": (
        "ftir", "fourier transform infrared", "sem", "scanning electron microscopy",
        "fluorescence", "microscopy", "afm", "chemical bond", "functional group",
        "microstructure", "phase morphology",
    ),
    "moisture_aging_durability": (
        "moisture", "water damage", "aging", "ageing", "freeze-thaw",
        "freeze thaw", "durability", "fatigue", "rutting",
    ),
    "service_field_relevance": (
        "service condition", "field performance", "field trial", "road construction",
        "pavement construction", "field construction", "traffic", "pavement section", "in situ",
    ),
    "review_background": (
        "review", "recent progress", "state of the art", "research gap",
        "knowledge gap", "bibliometric",
    ),
}

MECHANISM_LAYERS: set[str] = {"curing_demulsification", "microstructure_chemistry"}
DURABILITY_LAYERS: set[str] = {"moisture_aging_durability", "service_field_relevance"}
PERFORMANCE_LAYERS: set[str] = {
    "bonding_interface_performance", "emulsion_stability", "rheology",
    "curing_demulsification", "material_formulation",
}


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

def _normalize(text: str | None) -> str:
    return " ".join((text or "").lower().replace("_", " ").split())


def _contains_keyword(text: str, keyword: str) -> bool:
    kw = _normalize(keyword)
    if not kw:
        return False
    return re.search(rf"(?<![a-z0-9]){re.escape(kw)}(?![a-z0-9])", text) is not None


def _contains_any(text: str, keywords: tuple[str, ...]) -> bool:
    return any(_contains_keyword(text, k) for k in keywords)


# ---------------------------------------------------------------------------
# Public classification API
# ---------------------------------------------------------------------------

def classify_evidence_layers(text: str) -> list[str]:
    """Return evidence layers whose keywords match *text*."""
    normalized = _normalize(text)
    if not normalized:
        return []
    return [
        layer for layer, keywords in EVIDENCE_LAYER_KEYWORDS.items()
        if _contains_any(normalized, keywords)
    ]


def evidence_type_for_claim(text: str) -> str:
    """Map a claim to the highest-risk evidence type reviewers expect."""
    normalized = _normalize(text)
    layers = set(classify_evidence_layers(normalized))
    if _contains_any(normalized, ("mechanism", "microstructure", "chemical", "ftir")):
        return "mechanism"
    if layers & MECHANISM_LAYERS:
        return "mechanism"
    if _contains_any(normalized, ("durability", "moisture", "aging", "freeze", "service")):
        return "durability"
    if layers & DURABILITY_LAYERS:
        return "durability"
    if _contains_any(normalized, ("review", "gap", "progress", "state of the art")):
        return "review/positioning"
    if layers & PERFORMANCE_LAYERS:
        return "performance"
    return "primary evidence"


# ---------------------------------------------------------------------------
# Journal expansion
# ---------------------------------------------------------------------------

JOURNAL_FAMILIES: dict[str, str] = {
    "CBM": "Construction and Building Materials",
    "CBM-TRANSPORTATION": "Construction and Building Materials in Transportation",
    "CCC": "Cement and Concrete Composites",
    "CCR": "Cement and Concrete Research",
    "CSCM": "Case Studies in Construction Materials",
    "JMCE": "Journal of Materials in Civil Engineering",
    "JBE": "Journal of Building Engineering",
    "MAS": "Materials and Structures",
    "JCP": "Journal of Cleaner Production",
    "RCR": "Resources, Conservation and Recycling",
    "FUEL": "Fuel",
    "MCR": "Magazine of Concrete Research",
    "RMPD": "Road Materials and Pavement Design",
    "IJPE": "International Journal of Pavement Engineering",
    "JRE": "Journal of Road Engineering",
}

DEFAULT_JOURNAL_FAMILIES: tuple[str, ...] = (
    "CBM", "CCC", "CCR", "JBE", "RMPD", "IJPE", "JRE", "CSCM", "JCP",
)


def expand_journal_terms(aliases: list[str]) -> list[str]:
    """Expand journal aliases to canonical full titles."""
    expanded: list[str] = []
    for alias in aliases:
        norm = _normalize(alias).replace("-", " ").replace("_", " ")
        canonical = JOURNAL_FAMILIES.get(alias.upper())
        if canonical and canonical not in expanded:
            expanded.append(canonical)
        elif alias.strip() and alias.strip() not in expanded:
            expanded.append(alias.strip())
    return expanded or [JOURNAL_FAMILIES[k] for k in DEFAULT_JOURNAL_FAMILIES]


# ---------------------------------------------------------------------------
# Default claims & CSV field names
# ---------------------------------------------------------------------------

DEFAULT_CLAIMS: list[str] = [
    "Research gap and novelty",
    "Material design rationale",
    "Performance improvement",
    "Mechanism explanation",
    "Durability or service-condition relevance",
]

# Superset of fields used by both scripts (includes candidate_doi / candidate_year).
CSV_FIELDS: list[str] = [
    "claim_id", "priority", "claim_or_need", "evidence_layer",
    "source_role", "source_quality", "mechanism_directness",
    "durability_relevance", "service_relevance", "reader_anchor",
    "figure_handoff", "reviewer_risk", "search_query", "target_journals",
    "evidence_type", "candidate_source", "candidate_doi", "candidate_year",
    "status", "manuscript_location", "risk_note",
]


# ---------------------------------------------------------------------------
# Claim / item helpers
# ---------------------------------------------------------------------------

def split_items(value: str) -> list[str]:
    """Split a comma/semicolon string into a deduplicated list."""
    items: list[str] = []
    for item in value.replace(";", ",").split(","):
        cleaned = item.strip()
        if cleaned and cleaned not in items:
            items.append(cleaned)
    return items


def read_claims(path: str | None) -> list[str]:
    """Read claims from a text file, or return defaults when *path* is None."""
    if not path:
        return DEFAULT_CLAIMS
    claims_path = Path(path)
    if not claims_path.exists():
        raise FileNotFoundError(f"claims file not found: {path}")
    lines = claims_path.read_text(encoding="utf-8").splitlines()
    claims = [line.strip(" -\t") for line in lines if line.strip()]
    return claims or DEFAULT_CLAIMS


# ---------------------------------------------------------------------------
# Evidence-type helper functions
# ---------------------------------------------------------------------------

def default_layer_for_evidence_type(evidence_type: str) -> str:
    """Return the default evidence layer for a given evidence type."""
    mapping = {
        "mechanism": "microstructure_chemistry",
        "durability": "moisture_aging_durability",
        "review/positioning": "review_background",
        "performance": "bonding_interface_performance",
    }
    return mapping.get(evidence_type, "material_formulation")


def source_role_for_evidence_type(evidence_type: str) -> str:
    if evidence_type == "review/positioning":
        return "review evidence"
    return "primary experimental evidence"


def mechanism_directness(evidence_type: str) -> str:
    if evidence_type == "mechanism":
        return "direct mechanism evidence needed"
    return "not a mechanism claim"


def durability_relevance(evidence_type: str, layer: str) -> str:
    if evidence_type == "durability" or layer in DURABILITY_LAYERS:
        return "direct durability evidence needed"
    return "not a durability claim"


def service_relevance(layer: str) -> str:
    if layer == "service_field_relevance":
        return "direct service or field evidence needed"
    return "lab-scale unless field evidence is mapped"


# ---------------------------------------------------------------------------
# Query builder
# ---------------------------------------------------------------------------

def build_query(topic: str, claim: str, journals: list[str]) -> str:
    """Build a Boolean search query string for a given topic/claim/journals."""
    journal_terms = " OR ".join(f'"{j}"' for j in expand_journal_terms(journals))
    claim_terms = claim.replace("Research gap and novelty", "review OR recent progress")
    return f'("{topic}") AND ({claim_terms}) AND ({journal_terms})'


# ---------------------------------------------------------------------------
# Row builder
# ---------------------------------------------------------------------------

def build_claim_row(
    idx: int,
    claim: str,
    evidence_type: str,
    layer: str,
    search_query: str,
    target_journals: list[str],
    *,
    candidate_source: str = "[search needed]",
    candidate_doi: str = "",
    candidate_year: str = "",
    status: str = "search needed",
    risk_note: str = "Do not make this claim until a confirmed source is mapped.",
) -> dict[str, str]:
    """Build a complete citation-matrix row dictionary."""
    return {
        "claim_id": f"CIT-{idx:03d}",
        "priority": "must-fix" if idx <= 2 else "strengthen",
        "claim_or_need": claim,
        "evidence_layer": layer,
        "source_role": source_role_for_evidence_type(evidence_type),
        "source_quality": "screening needed",
        "mechanism_directness": mechanism_directness(evidence_type),
        "durability_relevance": durability_relevance(evidence_type, layer),
        "service_relevance": service_relevance(layer),
        "reader_anchor": "[reader anchor needed]",
        "figure_handoff": "not assessed",
        "reviewer_risk": "must-fix" if idx <= 2 else "strengthen",
        "search_query": search_query,
        "target_journals": "; ".join(target_journals),
        "evidence_type": evidence_type,
        "candidate_source": candidate_source,
        "candidate_doi": candidate_doi,
        "candidate_year": candidate_year,
        "status": status,
        "manuscript_location": "[assign section]",
        "risk_note": risk_note,
    }
