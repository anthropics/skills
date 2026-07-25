"""Journal aliases for materials and pavement-materials searches."""

from __future__ import annotations

from collections.abc import Iterable


JOURNAL_FAMILIES: dict[str, tuple[str, tuple[str, ...]]] = {
    "CBM": (
        "Construction and Building Materials",
        ("cbm", "construction and building materials"),
    ),
    "CBM-TRANSPORTATION": (
        "Construction and Building Materials in Transportation",
        (
            "cbm in transportation",
            "construction and building materials in transportation",
        ),
    ),
    "CCC": (
        "Cement and Concrete Composites",
        ("ccc", "cement and concrete composites"),
    ),
    "CCR": (
        "Cement and Concrete Research",
        ("ccr", "cement and concrete research"),
    ),
    "CSCM": (
        "Case Studies in Construction Materials",
        ("cscm", "case studies in construction materials"),
    ),
    "JMCE": (
        "Journal of Materials in Civil Engineering",
        ("jmce", "asce jmce", "journal of materials in civil engineering"),
    ),
    "JBE": (
        "Journal of Building Engineering",
        ("jbe", "journal of building engineering"),
    ),
    "MAS": (
        "Materials and Structures",
        ("mas", "materials and structures", "rilem materials and structures"),
    ),
    "JCP": (
        "Journal of Cleaner Production",
        ("jcp", "journal of cleaner production"),
    ),
    "RCR": (
        "Resources, Conservation and Recycling",
        ("rcr", "resources conservation and recycling", "resources, conservation and recycling"),
    ),
    "FUEL": (
        "Fuel",
        ("fuel",),
    ),
    "MCR": (
        "Magazine of Concrete Research",
        ("mcr", "magazine of concrete research"),
    ),
    "RMPD": (
        "Road Materials and Pavement Design",
        ("rmpd", "road materials and pavement design"),
    ),
    "IJPE": (
        "International Journal of Pavement Engineering",
        ("ijpe", "international journal of pavement engineering"),
    ),
    "JRE": (
        "Journal of Road Engineering",
        ("jre", "journal of road engineering"),
    ),
}

DEFAULT_JOURNAL_FAMILIES = ("CBM", "CCC", "CCR", "JBE", "RMPD", "IJPE", "JRE", "CSCM", "JCP")


def _normalize(value: str) -> str:
    return " ".join(value.strip().lower().replace("_", " ").replace("-", " ").split())


def normalize_to_list(value: str | Iterable[str] | None) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        return [item.strip() for item in value.replace(";", ",").split(",") if item.strip()]
    return [str(item).strip() for item in value if str(item).strip()]


def canonical_journal_family(value: str) -> str:
    """Return the canonical journal name for an alias, or the stripped input."""

    normalized = _normalize(value)
    for alias, (canonical, alternatives) in JOURNAL_FAMILIES.items():
        if normalized == _normalize(alias) or normalized in {_normalize(item) for item in alternatives}:
            return canonical
        if normalized == _normalize(canonical):
            return canonical
    return value.strip()


def expand_journal_terms(value: str | Iterable[str] | None) -> list[str]:
    """Expand aliases to canonical journal titles, preserving unknown terms."""

    aliases = normalize_to_list(value) or list(DEFAULT_JOURNAL_FAMILIES)
    expanded: list[str] = []
    for alias in aliases:
        canonical = canonical_journal_family(alias)
        if canonical and canonical not in expanded:
            expanded.append(canonical)
    return expanded
