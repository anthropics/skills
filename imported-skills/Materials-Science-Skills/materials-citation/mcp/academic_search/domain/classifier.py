"""Evidence-layer classification for materials papers and claims."""

from __future__ import annotations

import re


EVIDENCE_LAYER_KEYWORDS: dict[str, tuple[str, ...]] = {
    "material_formulation": (
        "waterborne epoxy",
        "epoxy resin",
        "epoxy dosage",
        "resin dosage",
        "formulation",
        "modifier content",
        "emulsifier",
        "mix design",
        "material design",
    ),
    "emulsion_stability": (
        "emulsion stability",
        "storage stability",
        "zeta potential",
        "particle size",
        "settlement",
        "segregation",
        "sieve residue",
        "stability test",
    ),
    "bonding_interface_performance": (
        "bonding",
        "bond strength",
        "pull-off",
        "pull off",
        "interface",
        "interlayer",
        "adhesion",
        "adhesive",
        "tack coat",
        "shear strength",
        "direct tension",
    ),
    "rheology": (
        "rheology",
        "rheological property",
        "viscosity",
        "brookfield",
        "flow curve",
        "shear rate",
        "dsr",
        "dynamic shear rheometer",
    ),
    "curing_demulsification": (
        "demulsification",
        "demulsify",
        "breaking behavior",
        "breaking rate",
        "emulsion breaking",
        "epoxy curing",
        "curing reaction",
        "crosslink",
        "cross-link",
        "amine",
        "epoxy network",
        "gel time",
        "phase compatibility",
    ),
    "microstructure_chemistry": (
        "ftir",
        "fourier transform infrared",
        "sem",
        "scanning electron microscopy",
        "fluorescence",
        "microscopy",
        "afm",
        "chemical bond",
        "functional group",
        "microstructure",
        "phase morphology",
    ),
    "moisture_aging_durability": (
        "moisture",
        "water damage",
        "aging",
        "ageing",
        "freeze-thaw",
        "freeze thaw",
        "durability",
        "fatigue",
        "rutting",
    ),
    "service_field_relevance": (
        "service condition",
        "field performance",
        "field trial",
        "road construction",
        "pavement construction",
        "field construction",
        "traffic",
        "pavement section",
        "in situ",
    ),
    "review_background": (
        "review",
        "recent progress",
        "state of the art",
        "research gap",
        "knowledge gap",
        "bibliometric",
    ),
}

EVIDENCE_LAYER_ALIASES: dict[str, str] = {
    "bonding_interface": "bonding_interface_performance",
    "demulsification": "curing_demulsification",
    "epoxy_curing": "curing_demulsification",
    "ftir_sem_fluorescence_rheology": "microstructure_chemistry",
    "moisture_aging_service": "moisture_aging_durability",
    "review_positioning": "review_background",
    "storage_stability": "emulsion_stability",
    "viscosity": "rheology",
}

MECHANISM_LAYERS = {"curing_demulsification", "microstructure_chemistry"}
PERFORMANCE_LAYERS = {
    "bonding_interface_performance",
    "emulsion_stability",
    "rheology",
    "curing_demulsification",
    "material_formulation",
}
DURABILITY_LAYERS = {"moisture_aging_durability", "service_field_relevance"}


def _normalize(text: str | None) -> str:
    return " ".join((text or "").lower().replace("_", " ").split())


def _contains_keyword(text: str, keyword: str) -> bool:
    normalized_keyword = _normalize(keyword)
    if not normalized_keyword:
        return False
    pattern = rf"(?<![a-z0-9]){re.escape(normalized_keyword)}(?![a-z0-9])"
    return re.search(pattern, text) is not None


def _contains_any(text: str, keywords: tuple[str, ...]) -> bool:
    return any(_contains_keyword(text, keyword) for keyword in keywords)


def canonical_evidence_layer(layer: str | None) -> str | None:
    """Return the current WER-EA evidence layer name for legacy aliases."""

    normalized = _normalize(layer).replace(" ", "_")
    if not normalized:
        return None
    return EVIDENCE_LAYER_ALIASES.get(normalized, normalized)


def classify_evidence_layers(text: str | None) -> list[str]:
    """Classify text into materials evidence layers."""

    normalized = _normalize(text)
    if not normalized:
        return []

    layers: list[str] = []
    for layer, keywords in EVIDENCE_LAYER_KEYWORDS.items():
        if _contains_any(normalized, keywords):
            layers.append(layer)
    return layers


def evidence_type_for_claim(text: str | None) -> str:
    """Map a claim to the highest-risk evidence type reviewers are likely to expect.

    Priority is intentional: mechanism claims require direct mechanistic evidence,
    then durability claims require service/aging evidence, then review positioning,
    then performance evidence. This avoids upgrading performance-only results into
    unsupported mechanisms.
    """

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
