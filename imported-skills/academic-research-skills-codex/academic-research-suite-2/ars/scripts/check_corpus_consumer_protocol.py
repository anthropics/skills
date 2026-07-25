#!/usr/bin/env python3
"""Lint corpus consumer protocol per spec §5.2 (v3.6.5).

Enforces nine invariants L1–L9. Manifest-driven for L3–L6.
Exit 0 on pass, exit 1 on fail. Prints aggregated failure list.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Callable

# Path.cwd() (not __file__) is intentional: fixture-based tests in
# scripts/adapters/tests/test_check_corpus_consumer_protocol.py invoke
# this lint via subprocess.run(..., cwd=fixture_repo) and rely on cwd
# to swap repo state. Path(__file__) would hard-code the real repo.
REPO_ROOT = Path.cwd()
MANIFEST_PATH = REPO_ROOT / "scripts" / "corpus_consumer_manifest.json"
REF_DOC_PATH = REPO_ROOT / "academic-pipeline" / "references" / "literature_corpus_consumers.md"
HANDOFF_SCHEMAS = REPO_ROOT / "shared" / "handoff_schemas.md"

STUB_MARKER = "<!-- LINT_STUB: skip_cross_check -->"
STUB_STATUS_LINE = "**Status:** Stub — implementation in PR-B (v3.6.5)"
DEFERRED_CAVEAT = "Consumer-side integration deferred to v3.6.5+"
REF_DOC_BACKPOINTER = "academic-pipeline/references/literature_corpus_consumers.md"

# Canonical (agent_basename, agent_path) tuples per release state. L8
# compares the full tuple set, not just basenames, so a future manifest
# cannot slip in a duplicate basename with a different path and have
# frozenset collapsing mask the closed-set match. The spec §5.2 L8
# language is "supported_consumers[] MUST exactly match" — we honour
# that on (basename, path), with extra defence against duplicate
# basename entries.
_BIBLIO_ENTRY = ("bibliography_agent", "deep-research/agents/bibliography_agent.md")
_STRAT_ENTRY = (
    "literature_strategist_agent",
    "academic-paper/agents/literature_strategist_agent.md",
)
PR_A_TUPLES = frozenset({_BIBLIO_ENTRY})
PR_B_TUPLES = frozenset({_BIBLIO_ENTRY, _STRAT_ENTRY})

# Basename-only sets retained for L2 cross-check (which iterates by basename).
PR_A_SET = frozenset(b for b, _ in PR_A_TUPLES)
PR_B_SET = frozenset(b for b, _ in PR_B_TUPLES)

PRE_SCREENED_LINE_MARKERS = (
    "PRE-SCREENED FROM USER CORPUS:",
    "Adapter:",
    "Snapshot date:",
    "Total entries scanned:",
    "Pre-screening result:",
    "Included:",
    "Excluded by inclusion / exclusion criteria:",
    "Skipped (criteria cannot be applied):",
    "citation_keys",
    # F3 conditional zero-hit note line (canonical per spec §3.2).
    "Zero-hit note (emit per F3 only when Included: 0)",
    # F4 inline-comment anchors (canonical per spec §3.2 + §4.2). These
    # ensure the F4a-c / F4d-f reproducibility surface is not silently
    # dropped from the template.
    "per F4a",
    "per F4b",
    "per F4c",
    "per F4d",
    "per F4e",
    "per F4f",
    "Note: presence in corpus does not imply inclusion",
)

IRON_RULE_TITLES = (
    "Iron Rule 1 — Same criteria",
    "Iron Rule 2 — No silent skip",
    "Iron Rule 3 — No corpus mutation",
    "Iron Rule 4 — Graceful fallback on parse failure",
)

STEP_HEADINGS = (
    "Step 0:",
    "Step 1:",
    "Step 2:",
    "Step 3:",
    "Step 4:",
)

# Each case marker is matched with an explicit boundary regex so that
# "case B" and "case B'" are distinct: substring matching would let
# "case B'" cover for a missing "case B" line.
STEP2_CASE_MARKERS = (
    ("case A", re.compile(r"\bcase A\b")),
    ("case B", re.compile(r"\bcase B(?![A-Za-z'])")),
    ("case B'", re.compile(r"\bcase B'")),
    ("case C", re.compile(r"\bcase C\b")),
)


def load_manifest() -> dict:
    return json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))


def manifest_basenames() -> frozenset[str]:
    return frozenset(c["agent_basename"] for c in load_manifest()["supported_consumers"])


def manifest_entry_tuples() -> tuple[tuple[str, str], ...]:
    """Return (agent_basename, agent_path) tuples in manifest order.

    A list, not a set, so duplicates are visible to the caller.
    """
    return tuple(
        (c["agent_basename"], c["agent_path"])
        for c in load_manifest()["supported_consumers"]
    )


def find_consumer_blocks(ref_text: str) -> dict[str, str]:
    """Return mapping basename -> block text (from `## Consumer: <basename>` heading
    to next `## ` heading or EOF)."""
    pattern = re.compile(r"^## Consumer:\s+(\S+)\s*$", re.MULTILINE)
    matches = list(pattern.finditer(ref_text))
    out: dict[str, str] = {}
    for i, m in enumerate(matches):
        start = m.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(ref_text)
        out[m.group(1)] = ref_text[start:end]
    return out


def _manifested_agent_paths() -> list[Path]:
    return [
        REPO_ROOT / c["agent_path"] for c in load_manifest()["supported_consumers"]
    ]


def check_l1() -> list[str]:
    if not REF_DOC_PATH.exists():
        return [f"L1: reference doc {REF_DOC_PATH.relative_to(REPO_ROOT)} does not exist"]
    return []


def check_l2() -> list[str]:
    if not REF_DOC_PATH.exists():
        return []  # L1 already failed
    text = REF_DOC_PATH.read_text(encoding="utf-8")
    blocks = find_consumer_blocks(text)
    failures: list[str] = []

    manifest_set = manifest_basenames()
    for basename in manifest_set:
        if basename not in blocks:
            failures.append(
                f"L2: manifest entry '{basename}' has no '## Consumer: {basename}' heading in reference doc"
            )

    for basename, block in blocks.items():
        is_stub = STUB_MARKER in block
        if is_stub:
            if STUB_STATUS_LINE not in block:
                failures.append(
                    f"L2: stub block '{basename}' has LINT_STUB marker but missing '{STUB_STATUS_LINE}'"
                )
            if basename in manifest_set:
                failures.append(
                    f"L2: '{basename}' is in manifest but block carries LINT_STUB marker (must be full block, not stub)"
                )
        else:
            if basename not in manifest_set:
                failures.append(
                    f"L2: '{basename}' has full consumer block but is not in manifest"
                )
    return failures


def check_l3() -> list[str]:
    failures: list[str] = []
    for agent_path in _manifested_agent_paths():
        if not agent_path.exists():
            failures.append(f"L3: manifest references missing file {agent_path.relative_to(REPO_ROOT)}")
            continue
        if REF_DOC_BACKPOINTER not in agent_path.read_text(encoding="utf-8"):
            failures.append(
                f"L3: {agent_path.relative_to(REPO_ROOT)} missing backpointer '{REF_DOC_BACKPOINTER}'"
            )
    return failures


def check_l4() -> list[str]:
    failures: list[str] = []
    for agent_path in _manifested_agent_paths():
        if not agent_path.exists():
            continue
        text = agent_path.read_text(encoding="utf-8")
        if "PRE-SCREENED FROM USER CORPUS:" not in text:
            failures.append(
                f"L4: {agent_path.relative_to(REPO_ROOT)} missing PRE-SCREENED template start"
            )
    return failures


def check_l5() -> list[str]:
    failures: list[str] = []
    for agent_path in _manifested_agent_paths():
        if not agent_path.exists():
            continue
        text = agent_path.read_text(encoding="utf-8")
        for title in IRON_RULE_TITLES:
            if title not in text:
                failures.append(
                    f"L5: {agent_path.relative_to(REPO_ROOT)} missing iron-rule title '{title}'"
                )
    return failures


def check_l6() -> list[str]:
    failures: list[str] = []
    for agent_path in _manifested_agent_paths():
        if not agent_path.exists():
            continue
        text = agent_path.read_text(encoding="utf-8")
        for heading in STEP_HEADINGS:
            if heading not in text:
                failures.append(
                    f"L6: {agent_path.relative_to(REPO_ROOT)} missing step heading '{heading}'"
                )
        for label, pattern in STEP2_CASE_MARKERS:
            if not pattern.search(text):
                failures.append(
                    f"L6: {agent_path.relative_to(REPO_ROOT)} missing Step 2 case marker '{label}'"
                )
    return failures


_PRE_SCREENED_BLOCK_RE = re.compile(
    r"```[a-z]*\s*\n(PRE-SCREENED FROM USER CORPUS:.*?)\n```",
    re.DOTALL,
)


def _extract_pre_screened_block(text: str) -> str | None:
    """Extract the fenced PRE-SCREENED template block. Returns None if absent.

    Marker checks must run against the template body, not the full file —
    otherwise unrelated prose mentions of a marker name (e.g.,
    \"citation_keys\" inside the truncation rule sentence) would mask a
    missing template line and L7 would falsely pass.
    """
    m = _PRE_SCREENED_BLOCK_RE.search(text)
    return m.group(1) if m else None


def check_l7() -> list[str]:
    failures: list[str] = []
    for agent_path in _manifested_agent_paths():
        if not agent_path.exists():
            continue
        text = agent_path.read_text(encoding="utf-8")
        rel = agent_path.relative_to(REPO_ROOT)

        block = _extract_pre_screened_block(text)
        if block is None:
            failures.append(
                f"L7: {rel} PRE-SCREENED template fenced block not found"
            )
        else:
            for marker in PRE_SCREENED_LINE_MARKERS:
                if marker not in block:
                    failures.append(
                        f"L7: {rel} PRE-SCREENED template missing line marker '{marker}'"
                    )

        # Truncation prose check stays scoped to the full file: the spec §5.2
        # L7 places this prose in surrounding text, not inside the template.
        if "truncation rule" not in text.lower():
            failures.append(
                f"L7: {rel} missing 'truncation rule' prose mention (spec §5.2 L7)"
            )
    return failures


def check_l8() -> list[str]:
    failures: list[str] = []
    rel = HANDOFF_SCHEMAS.relative_to(REPO_ROOT)

    entries = manifest_entry_tuples()

    # Duplicate-entry guard: a future PR cannot stuff in a second
    # bibliography_agent row pointing at a different path and have the
    # frozenset comparison below silently collapse the dup.
    if len(entries) != len(set(entries)):
        seen: dict[tuple[str, str], int] = {}
        dups: list[tuple[str, str]] = []
        for e in entries:
            seen[e] = seen.get(e, 0) + 1
            if seen[e] == 2:
                dups.append(e)
        failures.append(
            f"L8: manifest contains duplicate (agent_basename, agent_path) "
            f"entries: {dups}"
        )

    # Same-basename, different-path guard: the original codex-flagged
    # blind spot. supported_consumers[] MUST be unique on basename too.
    basenames = [b for b, _ in entries]
    if len(basenames) != len(set(basenames)):
        seen_b: dict[str, int] = {}
        dup_basenames = []
        for b in basenames:
            seen_b[b] = seen_b.get(b, 0) + 1
            if seen_b[b] == 2:
                dup_basenames.append(b)
        failures.append(
            f"L8: manifest contains duplicate agent_basename entries (with "
            f"differing agent_path): {dup_basenames}. Each consumer must "
            f"appear exactly once."
        )

    entry_set = frozenset(entries)
    if entry_set not in (PR_A_TUPLES, PR_B_TUPLES):
        failures.append(
            f"L8: manifest does not match a known release state. "
            f"Got {sorted(entries)}; expected "
            f"{sorted(PR_A_TUPLES)} (PR-A) or {sorted(PR_B_TUPLES)} (PR-B)."
        )
        return failures

    if not HANDOFF_SCHEMAS.exists():
        failures.append(f"L8: {rel} does not exist")
        return failures

    text = HANDOFF_SCHEMAS.read_text(encoding="utf-8")

    if entry_set == PR_A_TUPLES:
        # Caveat MUST remain in PR-A; retirement is forbidden until PR-B
        if DEFERRED_CAVEAT not in text:
            failures.append(
                f"L8: PR-A pre-release state requires deferred caveat to remain in "
                f"{rel}; caveat retirement is forbidden until "
                f"literature_strategist_agent ships in PR-B"
            )
    else:  # PR_B_TUPLES
        if DEFERRED_CAVEAT in text:
            failures.append(
                f"L8: PR-B release state requires deferred caveat to be retired in {rel}"
            )
        if REF_DOC_BACKPOINTER not in text:
            failures.append(
                f"L8: PR-B release state requires backpointer "
                f"'{REF_DOC_BACKPOINTER}' in {rel}"
            )
    return failures


def check_l9() -> list[str]:
    if not REF_DOC_PATH.exists():
        return []  # L1 already failed
    text = REF_DOC_PATH.read_text(encoding="utf-8")
    failures: list[str] = []
    if "<!-- BAD -->" not in text:
        failures.append(
            f"L9: reference doc missing '<!-- BAD -->' marker (Iron Rule 2 example pair)"
        )
    if "<!-- GOOD -->" not in text:
        failures.append(
            f"L9: reference doc missing '<!-- GOOD -->' marker (Iron Rule 2 example pair)"
        )
    return failures


CHECKS: list[tuple[str, Callable[[], list[str]]]] = [
    ("L1", check_l1),
    ("L2", check_l2),
    ("L3", check_l3),
    ("L4", check_l4),
    ("L5", check_l5),
    ("L6", check_l6),
    ("L7", check_l7),
    ("L8", check_l8),
    ("L9", check_l9),
]


def main() -> int:
    all_failures: list[str] = []
    for name, fn in CHECKS:
        try:
            failures = fn()
        except Exception as exc:
            all_failures.append(f"{name}: check raised {type(exc).__name__}: {exc}")
            continue
        all_failures.extend(failures)

    if all_failures:
        print("Corpus consumer protocol lint FAILED:", file=sys.stderr)
        for f in all_failures:
            print(f"  - {f}", file=sys.stderr)
        return 1

    print("Corpus consumer protocol lint OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
