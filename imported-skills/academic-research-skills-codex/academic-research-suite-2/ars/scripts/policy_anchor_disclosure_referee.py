#!/usr/bin/env python3
"""#108 policy-anchor disclosure renderer — executable spec / referee.

This module is **not** the production renderer. The production renderer is
LLM-prose at runtime when the user invokes `disclosure` mode with
`--policy-anchor=<a>`. This referee codifies the protocol's deterministic
decision logic — §3 G10 7-row precedence table, §4 auto-promotion
forbiddance, and the per-anchor invariant predicates (G2/G5/G7/G8/G9) — so
that:

1. The conformance test suite (`test_policy_anchor_disclosure.py`) can
   exercise every (input × expected output) combination deterministically.
2. The protocol doc and the referee stay in sync — when the protocol's
   §2 table changes, this module must change with it; the test suite
   catches drift.

References:
- Decision Doc §3 (G10 7-row precedence table), §4.3 (8 invariants),
  §4.4 (11 open concerns).
- `academic-paper/references/policy_anchor_disclosure_protocol.md` §§2-7.
- Implementation spec §3 (resolved-paths table).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable

CANONICAL_ANCHORS = ("prisma-trAIce", "icmje", "nature", "ieee")
SLR_MODES = ("systematic-review", "slr")
NATURE_VENUE_NAMES = (
    "Nature",
    "Nature Portfolio",
    "Nature (Nature Publishing Group)",
    "Nature Publishing Group",
)
# Prefix family for Nature Portfolio journals (Nature Medicine, Nature
# Communications, Nature Climate Change, ...). All inherit the same
# parent AI policy, so venue=<any Nature Portfolio journal> +
# policy_anchor=nature is the only consistent (venue, anchor) pair.
NATURE_VENUE_PREFIXES = ("Nature ",)
VALID_CATEGORY_STATES = frozenset({"USED", "NOT USED", "UNCERTAIN"})

# G7 invariant: anchor-specific copyediting carve-out semantics.
# 'eliminate' = no disclosure under carve-out; 'downgrade' = disclosure
# preserved at same location with weaker strength; 'out_of_scope' =
# anchor framework does not address copyediting; 'not_addressed' =
# anchor policy explicitly silent on copyediting.
COPYEDITING_CARVEOUT_SEMANTICS: dict[str, str] = {
    "nature": "eliminate",
    "ieee": "downgrade",
    "prisma-trAIce": "out_of_scope",
    "icmje": "not_addressed",
}

# G9 invariant: each anchor's image-rights regime stays distinct; the
# renderer must not unify them into a single boolean.
IMAGE_RIGHTS_REGIMES: dict[str, str] = {
    "prisma-trAIce": "data_handling_adjacency",
    "icmje": "text_attribution_no_ai_primary",
    "nature": "default_deny_with_carveouts",
    "ieee": "acknowledgments_only",
}


def is_nature_portfolio_venue(venue: str) -> bool:
    if venue in NATURE_VENUE_NAMES:
        return True
    return any(venue.startswith(p) for p in NATURE_VENUE_PREFIXES)


class TrackGateError(RuntimeError):
    """G2 invariant: --policy-anchor=prisma-trAIce requires slr_lineage=true
    or mode=<slr> input."""


class AutoPromotionForbidden(RuntimeError):
    """G3/G10 invariant: a still-UNCERTAIN category must not be rendered
    as though USED in any anchor output."""


class PairedMandateViolation(RuntimeError):
    """G8 invariant: IEEE render emits level_of_involvement and
    affected_sections together, or neither — emitting one without the
    other is non-conformant."""


class VenueAnchorConflict(RuntimeError):
    """§4.4 #7: --venue and --policy-anchor that map to incompatible
    placement / phrasing requirements must be rejected with explicit
    error; silent precedence is forbidden."""


class InvalidPolicyAnchor(ValueError):
    """policy_anchor outside CANONICAL_ANCHORS (closed enum)."""


class InvalidCategoryState(ValueError):
    """Category state outside {USED, NOT USED, UNCERTAIN}."""


class SelectorUnsupplied(ValueError):
    """Neither venue nor policy_anchor supplied — disclosure mode
    requires one selector. Default to None on both fields so a bare
    RendererInput() does not silently render under a single anchor."""


@dataclass(frozen=True)
class RendererInput:
    """Flat runtime input — no corpus-entry-level fields per G1 invariant."""

    ai_used: bool | None = None
    categories: dict[str, str] = field(default_factory=dict)
    policy_anchor: str | None = None
    venue: str | None = None
    slr_lineage: bool = False
    mode_param: str | None = None
    tool_type: str = "LLM"
    methodological_in_slr: bool = True
    level_of_involvement: str | None = None
    affected_sections: list[str] | None = None


@dataclass(frozen=True)
class DisclosureDecision:
    """Whole-disclosure decision returned by `decide_disclosure_output`."""

    row: int
    kind: str
    track: str
    used_facets: tuple[str, ...] = ()
    uncertain_facets: tuple[str, ...] = ()


# ---------------------------------------------------------------------------
# §3 G10 7-row precedence table
# ---------------------------------------------------------------------------
def decide_disclosure_output(ri: RendererInput) -> DisclosureDecision:
    """Return the G10 7-row decision for the given runtime input.

    Implements the protocol's §2 table exactly: rows evaluated top to
    bottom; first match wins. Concern #10 bare-flag gate evaluated before
    row 4 admits the input.
    """
    _check_selector_supplied(ri)
    _check_policy_anchor_enum(ri)
    _check_category_states(ri)
    _check_venue_anchor_conflict(ri)
    _check_track_gate(ri)

    buckets: dict[str, set[str]] = {s: set() for s in VALID_CATEGORY_STATES}
    for k, v in ri.categories.items():
        buckets[v].add(k)
    used, uncertain, not_used = buckets["USED"], buckets["UNCERTAIN"], buckets["NOT USED"]

    # Venue-only invocation: defer to v3.2 flow. The referee's row
    # decision is meaningful only when an anchor is selected.
    if ri.policy_anchor is None:
        return DisclosureDecision(
            row=0,
            kind="delegated_to_venue_path",
            track=ri.venue or "<unset>",
        )

    track = ri.policy_anchor

    if ri.ai_used is False and used:
        return DisclosureDecision(row=1, kind="conflict_annotation", track=track)

    if ri.ai_used is False and not used and not uncertain:
        return DisclosureDecision(row=2, kind="no_ai_statement", track=track)

    if ri.ai_used is False and uncertain and not used:
        return DisclosureDecision(row=3, kind="tension_annotation", track=track)

    # Concern #10 substantive-content gate: ai_used=true with no USED
    # category forces v3.2 categorization rather than rendering an
    # anchor disclosure with no facts to render.
    if ri.ai_used is True and not used:
        return DisclosureDecision(
            row=4,
            kind="prompt_for_categorization",
            track=track,
            uncertain_facets=tuple(sorted(uncertain)),
        )

    if (ri.ai_used is True or used) and not (ri.ai_used is False and used):
        if ri.policy_anchor == "ieee":
            assert_ieee_pairing_conformant(
                level_of_involvement=ri.level_of_involvement,
                affected_sections=ri.affected_sections,
            )
        return DisclosureDecision(
            row=4,
            kind="anchor_render",
            track=track,
            used_facets=tuple(sorted(used)),
            uncertain_facets=tuple(sorted(uncertain)),
        )

    if uncertain and not used and ri.ai_used is None:
        return DisclosureDecision(row=5, kind="not_supplied_annotation", track=track)

    if not_used and not uncertain and not used and ri.ai_used is None:
        return DisclosureDecision(row=6, kind="silence", track=track)

    return DisclosureDecision(row=7, kind="not_supplied_annotation", track=track)


def _check_selector_supplied(ri: RendererInput) -> None:
    if ri.policy_anchor is None and ri.venue is None:
        raise SelectorUnsupplied(
            "neither policy_anchor nor venue supplied; the disclosure mode "
            "requires the user to specify one selector."
        )


def _check_policy_anchor_enum(ri: RendererInput) -> None:
    # Venue-only invocation: enum check does not apply; v3.2 owns it.
    if ri.policy_anchor is None:
        return
    if ri.policy_anchor not in CANONICAL_ANCHORS:
        raise InvalidPolicyAnchor(
            f"policy_anchor='{ri.policy_anchor}' is not in the canonical "
            f"closed enum {CANONICAL_ANCHORS}. Selectors are case-sensitive "
            "and must match exactly."
        )


def _check_category_states(ri: RendererInput) -> None:
    invalid = {
        k: v for k, v in ri.categories.items() if v not in VALID_CATEGORY_STATES
    }
    if invalid:
        raise InvalidCategoryState(
            f"category states must be in {sorted(VALID_CATEGORY_STATES)}; "
            f"got invalid entries {invalid}"
        )


def _check_venue_anchor_conflict(ri: RendererInput) -> None:
    """§4.4 #7: the only consistent pair is any Nature Portfolio venue
    + policy_anchor='nature'; every other pair raises so silent
    precedence is impossible."""
    if ri.venue is None or ri.policy_anchor is None:
        return
    # Consistent: any Nature Portfolio venue with nature anchor.
    if is_nature_portfolio_venue(ri.venue) and ri.policy_anchor == "nature":
        return
    # All other combinations where both selectors are supplied are
    # rejected by default.
    raise VenueAnchorConflict(
        f"venue='{ri.venue}' and --policy-anchor='{ri.policy_anchor}' map to "
        "different (or unmapped) placement / phrasing requirements. The only "
        "currently defined consistent pair is any Nature Portfolio venue "
        "(canonical labels or `Nature ` prefix) with policy_anchor='nature'. "
        "Drop one selector or reconcile."
    )


def _check_track_gate(ri: RendererInput) -> None:
    """G2 invariant: --policy-anchor=prisma-trAIce requires SLR lineage."""
    if ri.policy_anchor != "prisma-trAIce":
        return
    if ri.slr_lineage:
        return
    if ri.mode_param and ri.mode_param in SLR_MODES:
        return
    raise TrackGateError(
        "policy_anchor='prisma-trAIce' requires slr_lineage=True (pipeline) "
        "or mode_param='systematic-review' (cold-start). Silent fallback to "
        "general track is forbidden by §4.3 G2 invariant."
    )


# ---------------------------------------------------------------------------
# §4 auto-promotion forbiddance + helpers
# ---------------------------------------------------------------------------
def render_facet_as_used(category_state: str) -> str:
    """Render a single facet at USED strength — raises if input is still
    UNCERTAIN. Encodes the G3/G10 forbiddance as an executable invariant."""
    if category_state == "UNCERTAIN":
        raise AutoPromotionForbidden(
            "category state UNCERTAIN MUST NOT be rendered as USED. "
            "See §4.3 G3/G10 invariant and concern #6 resolution."
        )
    if category_state == "USED":
        return "<full-strength facet render>"
    return "<no render>"


# ---------------------------------------------------------------------------
# G5 invariant — three-gate prompt disclosure predicate
# ---------------------------------------------------------------------------
def prompt_disclosure_required(
    track: str, tool_type: str, methodological_in_slr: bool
) -> bool:
    """True iff all three G5 gates hold."""
    if track != "prisma-trAIce":
        return False
    if tool_type not in {"LLM", "GenAI"}:
        return False
    if not methodological_in_slr:
        return False
    return True


def copyediting_carveout_semantics(anchor: str) -> str:
    return COPYEDITING_CARVEOUT_SEMANTICS[anchor]


# ---------------------------------------------------------------------------
# G8 invariant — IEEE #5 + #6 paired mandate
# ---------------------------------------------------------------------------
def assert_ieee_pairing_conformant(
    level_of_involvement: str | None, affected_sections: list[str] | None
) -> None:
    """Raise PairedMandateViolation if one is supplied without the other."""
    has_level = bool(level_of_involvement)
    has_sections = bool(affected_sections)
    if has_level != has_sections:
        raise PairedMandateViolation(
            "IEEE #5 (level_of_involvement) and IEEE #6 (affected_sections) "
            "are a paired mandate. Emit both together or neither. See "
            "§4.3 G8 invariant + impl spec concern #4 resolution."
        )


def image_rights_regime(anchor: str) -> str:
    return IMAGE_RIGHTS_REGIMES[anchor]


def nature_image_outputs(images: Iterable[dict]) -> dict[str, list[dict]]:
    """§4.4 #5: Nature image disclosure emits two output channels (annotation
    block + suggested patch); ARS does not modify manuscript source
    autonomously, so no inline_modification channel exists."""
    images = list(images)
    annotation_block = []
    suggested_patch = []
    for img in images:
        if not img.get("ai_generated"):
            continue
        annotation_block.append(
            {"image_id": img["id"], "label": "AI-generated (Nature default-deny carve-out evaluation required)"}
        )
        suggested_patch.append(
            {
                "image_id": img["id"],
                "diff": "<suggested figure-metadata caption patch — apply at author discretion>",
            }
        )
    return {
        "annotation_block": annotation_block,
        "suggested_patch": suggested_patch,
    }
