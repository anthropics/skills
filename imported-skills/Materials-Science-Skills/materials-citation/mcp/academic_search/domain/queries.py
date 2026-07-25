"""Boolean query generation for materials literature searches."""

from __future__ import annotations

from collections.abc import Iterable

from .classifier import EVIDENCE_LAYER_KEYWORDS, canonical_evidence_layer
from .journals import expand_journal_terms, normalize_to_list


MATERIAL_TERMS: dict[str, tuple[str, ...]] = {
    "asphalt": (
        "emulsified asphalt",
        "bitumen emulsion",
        "waterborne epoxy",
        "modified asphalt",
        "tack coat",
        "pavement interlayer",
    ),
    "cement-concrete": (
        "cement",
        "concrete",
        "mortar",
        "hydration",
        "supplementary cementitious materials",
        "durability",
    ),
    "materials": (
        "construction materials",
        "civil engineering materials",
        "durability",
        "microstructure",
        "sustainability",
    ),
    "ceramics": (
        "ceramic",
        "alumina",
        "zirconia",
        "silicon carbide",
        "silicon nitride",
        "sintering",
        "advanced ceramic",
        "refractory",
    ),
    "thermal-insulation": (
        "thermal insulation",
        "aerogel",
        "thermal conductivity",
        "building insulation",
        "porous material",
        "heat transfer",
        "insulation material",
    ),
}


def _quote(value: str) -> str:
    escaped = value.replace("\\", "\\\\").replace('"', '\\"')
    return f'"{escaped}"'


def _or_group(values: Iterable[str]) -> str:
    unique: list[str] = []
    for value in values:
        cleaned = value.strip()
        if cleaned and cleaned not in unique:
            unique.append(cleaned)
    return " OR ".join(_quote(value) if " " in value else value for value in unique)


def suggest_queries(
    *,
    topic: str,
    journal_family: str | Iterable[str] | None = None,
    material_domain: str | None = "general",
    evidence_layer: str | None = None,
    year_range: str | None = None,
    limit: int = 6,
) -> list[dict[str, str]]:
    """Create journal- and evidence-aware Boolean search queries."""

    if not topic or not topic.strip():
        raise ValueError("topic is required")

    selected_layers = [
        canonical
        for layer in normalize_to_list(evidence_layer)
        if (canonical := canonical_evidence_layer(layer))
    ]
    if not selected_layers:
        selected_layers = [
            "bonding_interface_performance",
            "microstructure_chemistry",
            "moisture_aging_durability",
            "emulsion_stability",
            "curing_demulsification",
            "review_background",
        ]

    journals = expand_journal_terms(journal_family)
    material_keywords = MATERIAL_TERMS.get(material_domain or "materials", MATERIAL_TERMS["materials"])
    queries: list[dict[str, str]] = []

    for layer in selected_layers[: max(1, limit)]:
        layer_terms = EVIDENCE_LAYER_KEYWORDS.get(layer, (layer.replace("_", " "),))
        query_parts = [
            _quote(topic.strip()),
            f"({_or_group(layer_terms[:6])})",
            f"({_or_group(material_keywords[:5])})",
        ]
        if journals:
            query_parts.append(f"({_or_group(journals)})")
        query = " AND ".join(query_parts)
        queries.append(
            {
                "topic": topic.strip(),
                "evidence_layer": layer,
                "journal_terms": "; ".join(journals),
                "year_range": year_range or "",
                "query": query,
            }
        )
    return queries


def build_pubmed_query(
    query: str,
    *,
    journals: str | Iterable[str] | None = None,
    year_range: str | None = None,
) -> str:
    """Convert a Boolean query into PubMed syntax with journal/date filters."""

    parts = [f"({query.strip()})"] if query and query.strip() else []
    journal_terms = normalize_to_list(journals)
    if journal_terms:
        journal_group = " OR ".join(f'{_quote(journal)}[Journal]' for journal in journal_terms)
        parts.append(f"({journal_group})")
    date_filter = _pubmed_date_filter(year_range)
    if date_filter:
        parts.append(date_filter)
    return " AND ".join(parts)


def _pubmed_date_filter(year_range: str | None) -> str:
    if not year_range or "-" not in str(year_range):
        return ""
    start, end = [part.strip() for part in str(year_range).split("-", 1)]
    if start and end:
        return f"{start}:{end}[pdat]"
    if start:
        return f"{start}:3000[pdat]"
    if end:
        return f"1900:{end}[pdat]"
    return ""
