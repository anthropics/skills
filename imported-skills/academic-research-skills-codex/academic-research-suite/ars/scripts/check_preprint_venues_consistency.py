#!/usr/bin/env python3
"""#105 lint — PREPRINT_VENUES 10-server list must agree across files.

v3.7.3 spec §3.2 Vector 1 fixes the closed list at 10 preprint servers
(gemini review F6 / codex F13 expansion from initial 6). The list lives
in two places:

1. `deep-research/agents/bibliography_agent.md` § "Signal 1 —
   preprint_post_llm_inflection" — bullet list (prose source of truth
   the bibliography_agent reads at ingest time).
2. `scripts/contamination_signals.py` `PREPRINT_VENUES` frozenset — the
   migration tool's Python constant.

If these drift, post-hoc migration would surface different CONTAMINATED-
PREPRINT advisories than ingest-time computation. This lint extracts
both lists, compares as sorted sets, and fails on mismatch.

Exit codes:
  0 = lists agree
  1 = mismatch (prints both sets + the diff)
  2 = could not parse either file (file move / heading rename / regex break)
"""
from __future__ import annotations

import re
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
PROSE_PATH = REPO_ROOT / "deep-research" / "agents" / "bibliography_agent.md"
PYTHON_PATH = REPO_ROOT / "scripts" / "contamination_signals.py"


# Venue strings in the spec carry mixed casing + spaces (e.g.,
# "Research Square", "OSF Preprints"); normalize for comparison.
def _normalize(s: str) -> str:
    return " ".join(s.split())


def _extract_prose_venues(text: str) -> set[str]:
    """Pull the bullet list under § Signal 1.

    The prose block looks like:
        2. The entry's `venue` field ...:
           - arXiv
           - bioRxiv
           - medRxiv
           ...
           - TechRxiv

    We slice from "preprint_post_llm_inflection" heading to "Otherwise
    set to" sentinel, then pull every `- <name>` line whose name comes
    before any inline comment.
    """
    start = text.find("preprint_post_llm_inflection")
    end = text.find("Otherwise set to", start) if start >= 0 else -1
    if start < 0 or end < 0:
        raise RuntimeError(
            "could not locate Signal 1 section in bibliography_agent.md "
            "(heading or 'Otherwise set to' sentinel changed)"
        )
    block = text[start:end]
    venues: set[str] = set()
    for line in block.splitlines():
        m = re.match(r"^\s*-\s+([A-Za-z0-9][A-Za-z0-9 .]*?)(\s*\(.*)?$", line)
        if m:
            venues.add(_normalize(m.group(1)))
    return venues


def _extract_python_venues(text: str) -> set[str]:
    """Pull the items from the `PREPRINT_VENUES = frozenset({ ... })` literal."""
    m = re.search(
        r"PREPRINT_VENUES\s*=\s*frozenset\(\{([^}]+)\}\)",
        text,
        flags=re.DOTALL,
    )
    if not m:
        raise RuntimeError(
            "could not locate PREPRINT_VENUES literal in contamination_signals.py"
        )
    body = m.group(1)
    venues = {
        _normalize(s.strip().strip('"').strip("'"))
        for s in body.split(",")
        if s.strip().strip('"').strip("'")
    }
    return venues


def main() -> int:
    try:
        prose = _extract_prose_venues(PROSE_PATH.read_text(encoding="utf-8"))
        py = _extract_python_venues(PYTHON_PATH.read_text(encoding="utf-8"))
    except (FileNotFoundError, RuntimeError) as e:
        print(f"PREPRINT_VENUES lint ERROR: {e}", file=sys.stderr)
        return 2

    if prose == py:
        print(
            f"PREPRINT_VENUES lint OK: {len(prose)} venues agree across "
            f"bibliography_agent.md and contamination_signals.py."
        )
        return 0

    only_prose = sorted(prose - py)
    only_py = sorted(py - prose)
    print("PREPRINT_VENUES lint FAILED — venue list drift detected:", file=sys.stderr)
    if only_prose:
        print(f"  only in bibliography_agent.md: {only_prose}", file=sys.stderr)
    if only_py:
        print(f"  only in contamination_signals.py: {only_py}", file=sys.stderr)
    print(
        "Reconcile by updating both files in lockstep. Spec §3.2 Vector 1 + "
        "schema description in literature_corpus_entry.schema.json must also agree.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
