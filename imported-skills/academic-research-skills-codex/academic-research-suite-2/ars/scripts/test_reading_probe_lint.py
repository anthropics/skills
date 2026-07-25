"""Lint tests for the v3.5.1 opt-in Socratic reading-check probe.

Target spec: docs/design/2026-04-22-ars-v3.7.3-reading-check-probe-design.md §5.1.

These are file-content lints (grep / regex / structure assertions) against:
- deep-research/agents/socratic_mentor_agent.md §"Optional Reading Probe Layer"
- deep-research/references/socratic_mode_protocol.md §"Reading Probe"
- deep-research/SKILL.md §"Opt-in Reading Probe (v3.5.1)"
- academic-pipeline/references/process_summary_protocol.md §"Reading Probe Outcomes"

Pattern matches test_check_compliance_report.py — no LLM runtime, no subprocess fork,
just read file bytes and assert structural invariants.

Run standalone:
    python -m unittest scripts/test_reading_probe_lint.py -v

Run via suite:
    python -m unittest discover scripts/ -v
"""
from __future__ import annotations

import re
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

MENTOR_AGENT = REPO_ROOT / "deep-research" / "agents" / "socratic_mentor_agent.md"
SOCRATIC_PROTOCOL = REPO_ROOT / "deep-research" / "references" / "socratic_mode_protocol.md"
DEEP_RESEARCH_SKILL = (
    REPO_ROOT / "deep-research" / "WORKFLOW.md"
    if (REPO_ROOT / "deep-research" / "WORKFLOW.md").is_file()
    else REPO_ROOT / "deep-research" / "SKILL.md"
)
README_EN = REPO_ROOT / "README.md"
README_ZH = REPO_ROOT / "README.zh-TW.md"
PIPELINE_PROCESS_SUMMARY = REPO_ROOT / "academic-pipeline" / "references" / "process_summary_protocol.md"
COLLABORATION_RUBRIC = REPO_ROOT / "shared" / "collaboration_depth_rubric.md"
COMPLIANCE_SCHEMA = REPO_ROOT / "shared" / "schemas" / "compliance_report.schema.json"


PROBE_HEADING = "## Optional Reading Probe Layer"

REQUIRED_PROBE_SUBHEADINGS = [
    "### Activation",
    "### Candidate Paper Tracking",
    "### Probe Wording",
    "### Response Handling",
    "### Banned Phrases",
    "### Research Plan Summary Subsection",
]


def _extract_probe_section(text: str) -> str:
    """Return the probe layer section body, or empty string if the heading is absent.

    Isolates `## Optional Reading Probe Layer` through to (but not including)
    the next top-level `## ` heading. Callers should guard on truthiness before
    asserting on content, so a missing section fails loudly instead of quietly
    running assertions against garbage slices.
    """
    start = text.find(PROBE_HEADING)
    if start == -1:
        return ""
    end = text.find("\n## ", start + 1)
    return text[start:end] if end > -1 else text[start:]


class ReadingProbeLintTests(unittest.TestCase):
    """Spec §5.1 — 7 file-content lints for the reading-check probe."""

    def test_mentor_file_has_probe_section(self) -> None:
        """Mentor file contains §'Optional Reading Probe Layer' with 6 subsections."""
        text = MENTOR_AGENT.read_text(encoding="utf-8")
        self.assertIn("## Optional Reading Probe Layer", text,
                      f"{MENTOR_AGENT} missing §'Optional Reading Probe Layer' heading")
        # Required subsections — match spec §3.1-3.7 ordering
        for sub in REQUIRED_PROBE_SUBHEADINGS:
            self.assertIn(sub, text,
                          f"{MENTOR_AGENT} missing subsection {sub!r}")

    def test_env_var_name_consistent_across_repo(self) -> None:
        """ARS_SOCRATIC_READING_PROBE appears verbatim across agent/protocol/SKILL/READMEs.

        Catches upper-case drift (e.g. ARS_SOCRATIC_READINGPROBE) and typos; does
        not attempt to catch lower-case drift since spec mandates all-caps.
        """
        expected = "ARS_SOCRATIC_READING_PROBE"
        # Spec §5.1 item 2: "agent, protocol, SKILL, README".
        # process_summary_protocol is excluded — it carries the [READING-PROBE:]
        # pickup rule (tested separately by test_probe_tag_format), not the env var.
        files = [MENTOR_AGENT, SOCRATIC_PROTOCOL, DEEP_RESEARCH_SKILL, README_EN, README_ZH]
        for f in files:
            text = f.read_text(encoding="utf-8")
            self.assertIn(expected, text,
                          f"{f.relative_to(REPO_ROOT)} missing env var {expected!r}")
            # Police ONLY the READING-probe var's own casing/typos. Sibling
            # socratic env vars (e.g. ARS_SOCRATIC_ADJACENT_PROBE) are legitimate
            # and must not be mis-flagged as drift — match the READING stem only.
            wrong_cases = re.findall(r"\bARS_SOCRATIC_READING[_A-Z]*\b", text)
            for hit in wrong_cases:
                self.assertEqual(hit, expected,
                                 f"{f.relative_to(REPO_ROOT)} has case-drifted "
                                 f"env var {hit!r}, expected {expected!r}")

    def test_probe_gated_by_goal_oriented(self) -> None:
        """Mentor probe section states goal-oriented-only activation."""
        text = MENTOR_AGENT.read_text(encoding="utf-8")
        probe_section = _extract_probe_section(text)
        self.assertTrue(probe_section,
                        f"{MENTOR_AGENT.name}: §'{PROBE_HEADING}' section not found")
        # Required phrasing (spec §3.2 activation clause)
        self.assertRegex(probe_section,
                         r"goal[- ]oriented",
                         "probe section must state goal-oriented gating")

    def test_decline_is_zero_penalty(self) -> None:
        """Decline outcome is explicitly excluded from all 5 scoring channels."""
        text = MENTOR_AGENT.read_text(encoding="utf-8")
        probe_section = _extract_probe_section(text)
        self.assertTrue(probe_section,
                        f"{MENTOR_AGENT.name}: §'{PROBE_HEADING}' section not found")
        exclusions = [
            "Persistent-Agreement",
            "Conflict-Avoidance",
            "Premature-Convergence",
            "convergence signal",
            "intent classification",
        ]
        for chan in exclusions:
            self.assertIn(chan, probe_section,
                          f"probe section must mention {chan!r} in decline-zero-penalty clause")
        self.assertRegex(probe_section,
                         r"(no penalty|not penali[sz]ed)",
                         "probe section must state decline is not penalised")

    def test_probe_tag_format(self) -> None:
        """[READING-PROBE:] tag format is defined in mentor and picked up identically in process_summary_protocol."""
        mentor_text = MENTOR_AGENT.read_text(encoding="utf-8")
        process_text = PIPELINE_PROCESS_SUMMARY.read_text(encoding="utf-8")
        tag_prefix = "[READING-PROBE:"
        self.assertIn(tag_prefix, mentor_text,
                      f"{MENTOR_AGENT.name} must define {tag_prefix!r} tag format")
        self.assertIn(tag_prefix, process_text,
                      f"{PIPELINE_PROCESS_SUMMARY.name} must reference {tag_prefix!r} for Stage 6 pickup")
        for field in ["paper=", "outcome=", "turn="]:
            self.assertIn(field, mentor_text,
                          f"{MENTOR_AGENT.name} tag spec missing field {field!r}")
            self.assertIn(field, process_text,
                          f"{PIPELINE_PROCESS_SUMMARY.name} pickup rule missing field {field!r}")

    def test_no_probe_in_scoring_files(self) -> None:
        """Probe identifiers must not leak into scoring/rubric files; prevents probe becoming a gate."""
        # Candidate files where a probe-as-gate regression could land.
        # Hand-maintained; expand when new scoring/rubric files are added.
        # Glob-scan rejected to avoid false failures on unrelated shared/ files.
        scoring_files = []
        if COLLABORATION_RUBRIC.exists():
            scoring_files.append(COLLABORATION_RUBRIC)
        if COMPLIANCE_SCHEMA.exists():
            scoring_files.append(COMPLIANCE_SCHEMA)
        # Mentor convergence-signal subsection — scan outside the probe section
        mentor_text = MENTOR_AGENT.read_text(encoding="utf-8")
        probe_start = mentor_text.find(PROBE_HEADING)
        probe_end = mentor_text.find("\n## ", probe_start + 1) if probe_start > -1 else -1
        if probe_start > -1:
            mentor_without_probe = (
                mentor_text[:probe_start]
                + (mentor_text[probe_end:] if probe_end > -1 else "")
            )
        else:
            mentor_without_probe = mentor_text

        banned_identifiers = ["reading_probe", "READING-PROBE", "reading-probe"]
        for ident in banned_identifiers:
            self.assertNotIn(
                ident, mentor_without_probe,
                f"{MENTOR_AGENT.name} has {ident!r} leaking OUTSIDE §'{PROBE_HEADING}'"
            )
        for f in scoring_files:
            text = f.read_text(encoding="utf-8")
            for ident in banned_identifiers:
                self.assertNotIn(
                    ident, text,
                    f"{f.relative_to(REPO_ROOT)} contains {ident!r} — "
                    f"probe must not appear in scoring/rubric files"
                )

    def test_banned_praise_phrases(self) -> None:
        """Banned-phrases list contains the 8 exact quoted strings from spec §3.6; "check" absent."""
        text = MENTOR_AGENT.read_text(encoding="utf-8")
        start = text.find("### Banned Phrases")
        self.assertGreater(start, -1, "missing '### Banned Phrases' subheading")
        end = text.find("\n### ", start + 1)
        if end == -1:
            end = text.find("\n## ", start + 1)
        banned_section = text[start:end if end > -1 else len(text)]
        # Exact strings, quoted as in spec §3.6
        expected_banned = [
            '"correct"',
            '"right"',
            '"wrong"',
            '"good answer"',
            '"well said"',
            '"make sure"',
            '"verify"',
            '"prove"',
        ]
        for phrase in expected_banned:
            self.assertIn(phrase, banned_section,
                          f"banned-phrases list missing {phrase!r}")
        # (per spec §3.6 note — "check" has non-evaluative uses elsewhere in the section)
        self.assertNotRegex(
            banned_section,
            r'(?m)^\s*[-*]\s*["\'`]check["\'`]',
            "'check' must NOT appear as a list-item entry in banned-phrases list "
            "(per spec §3.6 explicit carve-out). Inline prose uses of `check` are fine."
        )


if __name__ == "__main__":
    unittest.main()
