"""Lint tests for the opt-in Socratic adjacent-framing probe.

Target spec: docs/design/2026-06-18-socratic-adjacent-framing-probe-spec.md.

File-content lints (read bytes + regex, no LLM runtime, no subprocess fork) against:
- deep-research/agents/socratic_mentor_agent.md §"Optional Adjacent-Framing Probe Layer"

Pattern matches scripts/test_reading_probe_lint.py.

Run standalone:
    python -m unittest scripts/test_adjacent_framing_probe_lint.py -v
"""
from __future__ import annotations

import re
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

MENTOR_AGENT = REPO_ROOT / "deep-research" / "agents" / "socratic_mentor_agent.md"
# Scoring / pipeline files the probe must NOT leak into:
COLLABORATION_RUBRIC = REPO_ROOT / "shared" / "collaboration_depth_rubric.md"
PIPELINE_PROCESS_SUMMARY = REPO_ROOT / "academic-pipeline" / "references" / "process_summary_protocol.md"

PROBE_HEADING = "## Optional Adjacent-Framing Probe Layer"
ENV_VAR = "ARS_SOCRATIC_ADJACENT_PROBE"

REQUIRED_PROBE_SUBHEADINGS = [
    "### Activation",
    "### Probe Wording",
    "### Response Handling",
    "### Banned Patterns",
]


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _extract_probe_section(text: str) -> str:
    """Return the bytes from PROBE_HEADING up to the next H2 (## ) or EOF."""
    start = text.find(PROBE_HEADING)
    if start == -1:
        return ""
    rest = text[start + len(PROBE_HEADING):]
    nxt = re.search(r"\n## ", rest)
    return rest[: nxt.start()] if nxt else rest


class TestAdjacentFramingProbeStructure(unittest.TestCase):
    def setUp(self) -> None:
        self.mentor_text = _read(MENTOR_AGENT)
        self.section = _extract_probe_section(self.mentor_text)

    def test_mentor_file_has_probe_section(self) -> None:
        self.assertIn(
            PROBE_HEADING,
            self.mentor_text,
            f"{MENTOR_AGENT.name} must contain '{PROBE_HEADING}'",
        )

    def test_required_subheadings_present(self) -> None:
        for sub in REQUIRED_PROBE_SUBHEADINGS:
            self.assertIn(
                sub, self.section, f"Adjacent-framing probe section missing '{sub}'"
            )

    def test_env_var_gates_the_layer(self) -> None:
        self.assertIn(
            ENV_VAR,
            self.section,
            f"Probe layer must be gated by env var {ENV_VAR}",
        )
        # The "=1" activation discipline must be explicit somewhere in the section.
        self.assertRegex(
            self.section,
            re.escape(ENV_VAR) + r"[^\n]*?(?:=|\bset to\b)[^\n]*?`?1`?",
            "Probe layer must specify the env var activates on the string '1'",
        )

    def test_banned_patterns_subheading_present(self) -> None:
        self.assertIn(
            "### Banned Patterns",
            self.section,
            "Probe section must carry an explicit '### Banned Patterns' block",
        )

    def test_verb_test_terms_named_in_ban(self) -> None:
        # The Kong L2 verb test must be named in the normative LAW SENTENCE so the
        # executing agent knows the law — not merely present somewhere in the region
        # (a table row label like "BAD (rank)" must NOT satisfy this check).
        ban_region = self.section[self.section.find("### Banned Patterns"):]
        law_match = re.search(r"must never\b[^\n]*", ban_region, re.IGNORECASE)
        self.assertIsNotNone(
            law_match,
            "Banned Patterns block must contain a 'must never ...' law sentence",
        )
        law_sentence = law_match.group(0).lower()
        for verb in ("propose", "rank", "select", "expand", "substitute"):
            self.assertIn(
                verb,
                law_sentence,
                f"Law sentence must name the forbidden verb '{verb}' (found region-wide but not in the law sentence = robustness gap)",
            )

    def test_probe_wording_block_has_no_leak_phrases(self) -> None:
        # The Probe Wording block (the legal probe SURFACE) must not contain
        # idea-proposing phrasing or mechanism-bearing facet words.
        start = self.section.find("### Probe Wording")
        end = self.section.find("### Response Handling")
        self.assertGreater(start, -1)
        self.assertGreater(end, start)
        wording = self.section[start:end].lower()
        banned = ["you could research", "more novel", "consider:", "could become",
                  "mediation angle", "mediating role"]
        for phrase in banned:
            self.assertNotIn(
                phrase, wording,
                f"Probe Wording block must not contain leak phrase {phrase!r}",
            )

    def test_good_row_facet_is_directionless(self) -> None:
        # The Banned Patterns GOOD row must not use a mechanism/valenced facet noun.
        ban_region = self.section[self.section.find("### Banned Patterns"):]
        good_line = ""
        for line in ban_region.splitlines():
            if line.strip().startswith("| GOOD"):
                good_line = line.lower()
                break
        self.assertTrue(good_line, "Banned Patterns table must have a GOOD row")
        for mech in ("mediating", "mediation", "-impact", "-burnout", "driver of", "effect of"):
            self.assertNotIn(
                mech, good_line,
                f"GOOD-row facet must be directionless; found mechanism term {mech!r}",
            )

    def test_log_tag_format_present(self) -> None:
        # The exact machine-readable tag prefix must appear verbatim.
        self.assertIn(
            "[ADJACENT-PROBE: surfaced=",
            self.section,
            "Probe section must define the [ADJACENT-PROBE: ...] log tag",
        )
        self.assertIn("anchor=internal_knowledge", self.section)

    def test_exploratory_gate_not_goal_oriented(self) -> None:
        # Guard against a copy-paste of the Reading Probe's goal-oriented gate.
        activation = self.section[: self.section.find("### Probe Wording")]
        self.assertIn("exploratory", activation.lower())
        self.assertNotRegex(
            activation,
            r"intent classification[^\n]*?goal-oriented",
            "Activation must gate on EXPLORATORY, not goal-oriented (Reading-Probe copy-paste bug)",
        )

    def test_probe_does_not_leak_into_scoring_files(self) -> None:
        # The probe tag must not appear in scoring / pipeline-summary files —
        # it is dialogue-layer only, surfaced for Stage 6 reflection by grep, not
        # embedded as a scored artifact.
        for path in (COLLABORATION_RUBRIC,):
            if path.exists():
                self.assertNotIn(
                    "ADJACENT-PROBE",
                    _read(path),
                    f"{path.name} must not embed the adjacent-probe tag (scoring leak)",
                )


if __name__ == "__main__":
    unittest.main()
