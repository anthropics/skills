#!/usr/bin/env python3
"""Shared title-similarity + retry-budget helpers for the v3.9.0 cross-index
triangulation clients.

Previously triple-implemented byte-equivalently in
`semantic_scholar_client.py`, `openalex_client.py`, and `crossref_client.py`.
Extracted in #128 (v3.9.1 housekeeping) to prevent sibling drift — any
threshold tuning or normalization rule change now happens in one place.

`_normalize_title` / `_similarity` stay byte-equivalent with the v3.7.3 /
v3.9.0 client implementations for every NON-dotted-acronym title; #431 §0.1
adds a dotted-acronym pre-pass that can only *raise* `_similarity` (taken via
`max`), plus the `exact_normalized_title` / `generic_title` identity helpers the
exact-title-or-bust gate (§0.12) reads. See `test_text_similarity.py` for the
similarity contract and `test_431_exact_or_bust.py` for the gate behavior.
"""
from __future__ import annotations

import re
import string
from difflib import SequenceMatcher


_PUNCT_TRANSLATION = str.maketrans({c: " " for c in string.punctuation})

# #431 §0.1: collapse a run of two-or-more `<letter>.` units at a word boundary
# (`R.A.G.` → `RAG`) BEFORE punctuation→whitespace, so a dotted acronym and its
# undotted spelling normalize byte-equal. `/`, `&`, and spaced initials
# (`D. H.`) are NOT dotted runs and stay untouched (`A/B`, `R&D`, `Q&A`).
_DOTTED_ACRONYM = re.compile(r"\b(?:[A-Za-z]\.){2,}")


# Per protocol: shared retry budget for the index clients. S2 / Crossref
# sleep a fixed _BACKOFF_SECONDS per 429; OpenAlex uses it as the base of
# an exponential backoff (2s → 4s → 8s, #495); arXiv does not use it — its
# 429 backoff is the 3s ToU pacing floor (_ARXIV_MIN_INTERVAL, #495).
_BACKOFF_SECONDS = 2.0
_MAX_RETRIES = 3


# Per PaperOrchestra (Song et al. 2026 Appx D.3) + protocol §"Query Patterns"
# Pattern 1: title-similarity threshold for "matched" verdict.
_TITLE_SIMILARITY_THRESHOLD = 0.70


def _normalize_title(s: str) -> str:
    """Per protocol §"Query Patterns" Pattern 1: 'case-insensitive, stripped
    of punctuation' before computing similarity. Punctuation becomes
    whitespace so token boundaries are preserved, then collapse runs of
    whitespace. The byte-equivalent base form for every non-dotted title."""
    cleaned = s.lower().translate(_PUNCT_TRANSLATION)
    return " ".join(cleaned.split())


def _normalize_title_acronym(s: str) -> str:
    """#431 §0.1: base normalization plus the dotted-acronym pre-pass. The
    dots inside a `<letter>.`-run span are stripped first (`R.A.G.` → `RAG`),
    then the base path runs. Provably additive over the dotted form only — any
    title with no dotted run normalizes identically to `_normalize_title`.

    This is the form `exact_normalized_title` compares on: under #431's
    exact-title-or-bust gate the equality (not the ratio) is load-bearing, so a
    legitimate `R.A.G.`/`RAG` acronym variant must reach byte-equality here. The
    base form alone leaves them 'r a g …' ≠ 'rag …' — a high ratio but NOT
    equal, which under the gate would wrongly fall to `unresolvable`."""
    collapsed = _DOTTED_ACRONYM.sub(lambda m: m.group(0).replace(".", ""), s)
    return _normalize_title(collapsed)


def _similarity(a: str, b: str) -> float:
    """`max` over the base and dotted-acronym normalizations (#431 §0.1,
    F4 non-destructive): the acronym pre-pass can only ever *raise* the score,
    so `D. H.` vs `D. H.` stays 1.000 (it would be 0.981 if the acronym form
    replaced the base form). For non-dotted titles both forms are byte-equal, so
    the second pass is skipped and the result is the pre-#431 single-form ratio."""
    a_base, b_base = _normalize_title(a), _normalize_title(b)
    base = SequenceMatcher(None, a_base, b_base).ratio()
    a_acr, b_acr = _normalize_title_acronym(a), _normalize_title_acronym(b)
    if a_acr == a_base and b_acr == b_base:  # no dotted run in either title
        return base
    return max(base, SequenceMatcher(None, a_acr, b_acr).ratio())


def exact_normalized_title(a: str, b: str) -> bool:
    """#431 §0.12.1: the one identity signal all four resolvers can compute.
    True iff the two titles are byte-equal under EITHER the base normalization
    OR the dotted-acronym-aware one. Both forms are checked (mirroring
    `_similarity`'s `max`, F4 non-destructive): the acronym pre-pass must only
    ever *add* matches, never drop one the base form already had. Checking only
    the acronym form would regress a punctuation-only variant where exactly one
    side is a contiguous initialism — `D.H. Lawrence` vs `D. H. Lawrence`
    normalizes byte-equal under the base form (`d h lawrence`) but NOT under the
    acronym form (`dh` vs `d h`), and would wrongly fall to `unresolvable`.
    Legitimate punctuation / case / subtitle-spacing / `R.A.G.`→`RAG` acronym
    variants all match here; a distinct related work (different subtitle, Part I
    vs Part II, a correction-notice prefix) matches under neither and stays
    `unresolvable` rather than a false `matched`."""
    return (
        _normalize_title(a) == _normalize_title(b)
        or _normalize_title_acronym(a) == _normalize_title_acronym(b)
    )


# #431 §0.12.2: the closed generic/section/type/notice set. `generic_title` is
# EXACT set-membership on the normalized title — NOT substring or endswith. A
# content title that merely begins with or contains a type word (`Case Report of
# a Rare Tumor`, `A Comprehensive Review`) has a normalized form ≠ the bare type
# word, so it is NOT generic and is not demoted. This list is the single source
# of truth (spec §0.12.2); the regression fixture pins `Short Communication` /
# `Editorial Comment` / `Case Report` / `Publisher Correction` (exact title + no
# ID) → `unresolvable`.
_GENERIC_TITLES = frozenset(
    _normalize_title(t)
    for t in (
        "editorial", "guest editorial", "editorial comment", "introduction",
        "preface", "foreword", "letter", "letters", "letter to the editor",
        "letters to the editor", "reply", "comment", "commentary", "response",
        "correspondence", "book review", "book reviews", "review", "news",
        "obituary", "in memoriam", "acknowledgements", "front matter",
        "back matter", "table of contents", "abstracts", "abstract",
        "proceedings", "keynote", "panel discussion", "workshop summary",
        "special issue", "untitled", "note", "notes", "highlights", "errata",
        "erratum", "corrigendum", "addendum", "author correction",
        "publisher correction", "retraction", "expression of concern",
        "short communication", "rapid communication", "brief communication",
        "short report", "brief report", "technical report", "meeting report",
        "conference report", "case report", "case study", "research article",
        "original article", "original research", "short paper", "perspective",
        "perspectives", "viewpoint", "opinion", "discussion", "summary",
        "conclusion", "conclusions", "abstract only", "supplementary material",
    )
)


def generic_title(title: str) -> bool:
    """#431 §0.12.2: True iff the normalized title is byte-equal to a member of
    the closed generic set. Under the exact-or-bust gate an exact title match
    that is *also* generic accepts only when an ID/DOI corroborates; otherwise
    it is `unresolvable` (a bare `Editorial` collides across thousands of
    distinct works)."""
    return _normalize_title(title) in _GENERIC_TITLES
