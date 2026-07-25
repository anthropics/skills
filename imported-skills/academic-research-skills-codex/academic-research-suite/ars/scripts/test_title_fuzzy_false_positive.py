#!/usr/bin/env python3
"""Resolver-boundary pin for #250 / #430 / #431 — distinct-work rejection.

#250 recorded a regression the citation-extraction gold set cannot catch: a
resolver's title fallback *accidentally* accepts a wrong record as `matched`.
The decision lives one layer below the gold set — in the client `title_search`
and `_resolve_doi_then_title`, which `run_evals.py` never executes — so the pin
must exercise the client HTTP path directly. (See the #250 finding for the trace.)

Until #431 these two assertions were marked `xfail(strict=True)`: a character-
level `SequenceMatcher.ratio() >= 0.70` over punctuation-stripped titles scores
DISTINCT works far above 0.70 when they share long substrings —

    "Deep Residual Learning for Image Recognition"
    "...for Image Recognition on Embedded Devices"          -> 0.815
    "Attention Is All You Need" vs "...Is Not All You Need" -> 0.926

— so a real-but-unindexed citation whose title search surfaced a *different*
near-identical paper was collapsed to `matched`, with no year/author re-check to
catch it.

#431's exact-title-or-bust pivot (spec §0.12) closes this at the resolver
boundary: the title fallback now promotes a candidate to `matched` ONLY when its
normalized title is byte-equal to the cited title. A superstring (extra tail
words) and a negation ("Not") are both NON-exact, so both correctly return no
match — the xfail markers are removed and these are now real passing assertions
(the strict-xfail flipped to XPASS the moment the criterion hardened, by design).

The 0.70 + exact-title criterion is shared (via `_text_similarity`) by the
Crossref / OpenAlex / Semantic Scholar / arXiv clients, so this is not
Crossref-specific; CrossrefClient is the representative because its
`title_search` is the most direct. The complementary acceptance matrix (a
legitimate exact / acronym / case variant still matches, F3 ordering, generic
gating, the resolver→reducer `unresolvable` chain) is in
`test_431_exact_or_bust.py`.

Run:
    PYTHONPATH=. python -m pytest scripts/test_title_fuzzy_false_positive.py -v
"""
from __future__ import annotations

import json
import sys
from unittest.mock import MagicMock, patch


def _mock_response(payload: dict) -> MagicMock:
    """Build a urlopen() context-manager mock returning `payload` as JSON.

    Mirrors the mock shape in test_crossref_client.py so this pin exercises the
    real client HTTP path, not a stub.
    """
    resp = MagicMock()
    resp.read.return_value = json.dumps(payload).encode("utf-8")
    resp.__enter__ = MagicMock(return_value=resp)
    resp.__exit__ = MagicMock(return_value=None)
    return resp


def test_superstring_title_is_rejected_as_distinct_work():
    """A cited work's title search surfaces a DIFFERENT paper whose title merely
    contains the cited title as a prefix. Correct verdict: no match (the cited
    work is genuinely unindexed). Under #431 the superstring is non-exact, so
    `title_search` returns None."""
    from crossref_client import CrossrefClient

    cited_title = "Deep Residual Learning for Image Recognition"
    # The only candidate the index returns is a real but DIFFERENT paper.
    surfaced_distinct_work = {
        "title": ["Deep Residual Learning for Image Recognition on Embedded Devices"],
        "DOI": "10.0000/not-the-cited-work",
    }
    payload = {"message": {"items": [surfaced_distinct_work]}}

    with patch("urllib.request.urlopen", return_value=_mock_response(payload)):
        client = CrossrefClient()
        result = client.title_search(cited_title)

    assert result is None, (
        "title_search accepted a distinct work (superstring title) as a match — "
        "false positive. The cited work is unindexed; the resolver surfaced a "
        "different paper."
    )


def test_negated_title_is_rejected_as_distinct_work():
    """A negation ("Not") flips a title's meaning but barely moves the
    character-level ratio (0.926). Correct verdict: no match. Under #431 the
    negated title is non-exact, so `title_search` returns None."""
    from crossref_client import CrossrefClient

    cited_title = "Attention Is All You Need"
    surfaced_distinct_work = {
        "title": ["Attention Is Not All You Need"],
        "DOI": "10.0000/different-negated-work",
    }
    payload = {"message": {"items": [surfaced_distinct_work]}}

    with patch("urllib.request.urlopen", return_value=_mock_response(payload)):
        client = CrossrefClient()
        result = client.title_search(cited_title)

    assert result is None, (
        "title_search accepted a semantically negated title as a match — "
        "false positive on a distinct work."
    )


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
