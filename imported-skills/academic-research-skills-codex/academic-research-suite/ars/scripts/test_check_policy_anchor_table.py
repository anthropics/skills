#!/usr/bin/env python3
"""Mutation tests for scripts/check_policy_anchor_table.py.

Each test mutates a known-good anchor-table snippet in a known-bad way and
asserts the validator reports the expected violation. The goal is to prove
the validator catches each documented bad case in
docs/design/2026-05-14-ai-disclosure-impl-spec.md §4.1 (policy_anchor_table
lint scope) and §4.4 #11 (G1 scope-narrowing).
"""
from __future__ import annotations

import sys
import textwrap
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))

import check_policy_anchor_table as cpat  # noqa: E402


_GOOD_TABLE = textwrap.dedent(
    """\
    # Policy Anchor Table

    ## Anchor: prisma-trAIce

    **Snapshot:** `prisma-trAIce:wayback=20260513075443` (sha256: f95fc59f…)

    | # | Field | Source strength | Verbatim quote | Locator | Value type |
    |---|---|---|---|---|---|
    | 1 | AI tool name | explicit-recommend | "For each AI tool or system used: a. Specify the name, version number (if applicable), and developer/provider." | Table 1, M2.a | narrative |
    | 2 | AI tool version | explicit-recommend | "Specify the name, version number (if applicable), and developer/provider." | Table 1, M2.a | narrative |
    | 3 | AI tool developer / manufacturer | explicit-recommend | "Specify the name, version number (if applicable), and developer/provider." | Table 1, M2.a | narrative |
    | 4 | Stage / phase of use | explicit-recommend | "For each AI tool, clearly describe: a. The specific SLR stage(s) where it was applied." | Table 1, M3.a | narrative |
    | 5 | Specific task within stage | explicit-recommend | "b. The precise task(s) the AI was intended to perform at each stage." | Table 1, M3.b | narrative |
    | 6 | Affected manuscript sections / content locator | implicit | (inference passage) Items prescribe manuscript section per row. | Table 1 row headings | narrative |
    | 7 | Date(s) of use | not-addressed | — | — | — |
    | 8 | Prompts | explicit-recommend | "For each LLM/GenAI tool used, report: a. The full prompt(s) employed for each specific task." | Table 1, M6.a | narrative |
    | 9 | Human oversight method | explicit-recommend | "Describe the process of human interaction with and oversight of the AI tool(s) at each stage." | Table 1, M8.a–g | narrative |
    | 10 | Human responsibility statement | not-addressed | — | — | — |
    | 11 | Performance evaluation method | explicit-recommend | "Describe methods used to evaluate the AI tool(s) performance for the specific tasks within the review." | Table 1, M9 | narrative |
    | 12 | Performance evaluation results | explicit-recommend | "Report the results of any performance evaluations of the AI tool(s) for the specific tasks within the review." | Table 1, R2 | narrative |
    | 13 | Limitations / known failure modes | explicit-recommend | "Discuss any limitations encountered in using the AI tool(s)." | Table 1, D1 | narrative |
    | 14 | Disclosure location | implicit | (inference passage) Each Table 1 item is row-categorized by manuscript section. | Table 1 row groupings | narrative |
    | 15 | Copyediting exemption predicate | not-addressed | — | — | — |
    | 16 | AI-generated image / figure / content rights | implicit | (inference passage) M10 covers data handling. | Table 1, M10 | narrative |

    ## Anchor: icmje

    **Snapshot:** `icmje:wayback=20260513075516` (sha256: 52f9e6bc…)

    | # | Field | Source strength | Verbatim quote | Locator | Value type |
    |---|---|---|---|---|---|
    | 1 | AI tool name | implicit | (inference passage) Tool identity implied. | §V.A, paragraph 1 | narrative |
    | 2 | AI tool version | not-addressed | — | — | — |
    | 3 | AI tool developer / manufacturer | not-addressed | — | — | — |
    | 4 | Stage / phase of use | implicit | (inference passage) "How they used it" implies stage. | §V.A, paragraph 1 | narrative |
    | 5 | Specific task within stage | implicit | (inference passage) Same as #4 source. | §V.A, paragraph 1 | narrative |
    | 6 | Affected manuscript sections / content locator | not-addressed | — | — | — |
    | 7 | Date(s) of use | not-addressed | — | — | — |
    | 8 | Prompts | not-addressed | — | — | — |
    | 9 | Human oversight method | explicit-recommend | "Authors should carefully review and edit the AI-generated content as the output can be incorrect, incomplete, or biased." | §V.A, paragraph 1 | narrative |
    | 10 | Human responsibility statement | explicit-mandate | "Therefore, humans are responsible for any submitted material that included the use of AI-assisted technologies." | §V.A, paragraph 1 | narrative |
    | 11 | Performance evaluation method | not-addressed | — | — | — |
    | 12 | Performance evaluation results | not-addressed | — | — | — |
    | 13 | Limitations / known failure modes | not-addressed | — | — | — |
    | 14 | Disclosure location | explicit-recommend | "Authors who use such technology should describe, in both the cover letter and the submitted work in the appropriate section if applicable, how they used it" | §V.A, paragraph 1 | narrative |
    | 15 | Copyediting exemption predicate | not-addressed | — | — | — |
    | 16 | AI-generated image / figure / content rights | explicit-mandate | "Humans must ensure there is appropriate attribution of all quoted material, including full citations." | §V.A, paragraph 1 | narrative |

    ## Anchor: nature

    **Snapshot:** `nature:wayback=20260513075542` (sha256: cf691cba…)

    | # | Field | Source strength | Verbatim quote | Locator | Value type |
    |---|---|---|---|---|---|
    | 1 | AI tool name | implicit | (inference passage) Documentation requirement implies tool identity. | §AI authorship | narrative |
    | 2 | AI tool version | not-addressed | — | — | — |
    | 3 | AI tool developer / manufacturer | not-addressed | — | — | — |
    | 4 | Stage / phase of use | implicit | (inference passage) "Use" implies stage. | §AI authorship | narrative |
    | 5 | Specific task within stage | implicit | (inference passage) Methods documentation implies task. | §AI authorship | narrative |
    | 6 | Affected manuscript sections / content locator | implicit | (inference passage) Methods rule + caption rule. | §AI authorship; §Generative AI images | narrative |
    | 7 | Date(s) of use | not-addressed | — | — | — |
    | 8 | Prompts | not-addressed | — | — | — |
    | 9 | Human oversight method | explicit-mandate | "In all cases, there must be human accountability for the final version of the text and agreement from the authors that the edits reflect their original work." | §AI authorship | narrative |
    | 10 | Human responsibility statement | explicit-mandate | "an attribution of authorship carries with it accountability for the work, which cannot be effectively applied to LLMs" | §AI authorship | narrative |
    | 11 | Performance evaluation method | not-addressed | — | — | — |
    | 12 | Performance evaluation results | not-addressed | — | — | — |
    | 13 | Limitations / known failure modes | not-addressed | — | — | — |
    | 14 | Disclosure location | explicit-recommend | "Use of an LLM should be properly documented in the Methods section (and if a Methods section is not available, in a suitable alternative part) of the manuscript." | §AI authorship + §Generative AI images | narrative |
    | 15 | Copyediting exemption predicate | explicit-recommend | "The use of an LLM (or other AI-tool) for \\"AI assisted copy editing\\" purposes does not need to be declared." | §AI authorship | narrative |
    | 16 | AI-generated image / figure / content rights | explicit-mandate | "Springer Nature journals are unable to permit its use for publication." | §Generative AI images | narrative |

    ## Anchor: ieee

    **Snapshot:** `ieee:wayback=20260513075605` (sha256: 3ab8db50…)

    | # | Field | Source strength | Verbatim quote | Locator | Value type |
    |---|---|---|---|---|---|
    | 1 | AI tool name | explicit-mandate | "The AI system used shall be identified" | Paragraph 1, sentence 2 | narrative |
    | 2 | AI tool version | not-addressed | — | — | — |
    | 3 | AI tool developer / manufacturer | not-addressed | — | — | — |
    | 4 | Stage / phase of use | implicit | (inference passage) "Level at which" implies degree-of-involvement. | Paragraph 1, sentence 2 | narrative |
    | 5 | Specific task within stage | explicit-mandate | "specific sections of the article that use AI-generated content shall be identified and accompanied by a brief explanation regarding the level at which the AI system was used to generate the content" | Paragraph 1, sentence 2 | narrative |
    | 6 | Affected manuscript sections / content locator | explicit-mandate | "specific sections of the article that use AI-generated content shall be identified" | Paragraph 1, sentence 2 | narrative |
    | 7 | Date(s) of use | not-addressed | — | — | — |
    | 8 | Prompts | not-addressed | — | — | — |
    | 9 | Human oversight method | not-addressed | — | — | — |
    | 10 | Human responsibility statement | not-addressed | — | — | — |
    | 11 | Performance evaluation method | not-addressed | — | — | — |
    | 12 | Performance evaluation results | not-addressed | — | — | — |
    | 13 | Limitations / known failure modes | not-addressed | — | — | — |
    | 14 | Disclosure location | explicit-mandate | "shall be disclosed in the acknowledgments section of any article submitted to an IEEE publication" | Paragraph 1, sentence 1 | narrative |
    | 15 | Copyediting exemption predicate | explicit-recommend | "The use of AI systems for editing and grammar enhancement is common practice and, as such, is generally outside the intent of the above policy. In this case, disclosure as noted above is recommended." | Paragraph 2 | narrative |
    | 16 | AI-generated image / figure / content rights | implicit | (inference passage) Images/figures/code fold into general acknowledgments-disclosure mandate. | Paragraph 1, sentence 1 | narrative |
    """
)


class CheckPolicyAnchorTableGoldenPathTest(unittest.TestCase):
    def test_good_table_passes(self) -> None:
        violations = cpat.lint_text(_GOOD_TABLE)
        self.assertEqual(violations, [], msg=f"unexpected violations: {violations}")


class CheckPolicyAnchorTableMutationTests(unittest.TestCase):
    def test_missing_anchor_section_fails(self) -> None:
        bad = _GOOD_TABLE.replace("## Anchor: ieee", "## Anchor: not-an-anchor")
        violations = cpat.lint_text(bad)
        self.assertTrue(
            any("ieee" in v.lower() for v in violations),
            msg=f"expected ieee-missing violation; got {violations}",
        )

    def test_missing_field_row_fails(self) -> None:
        # Remove field #5 from PRISMA-trAIce. textwrap.dedent strips leading
        # indent so rows start at column 0; match the row prefix exactly.
        lines = _GOOD_TABLE.split("\n")
        bad_lines = [
            line for line in lines if not line.lstrip().startswith("| 5 | Specific task")
        ]
        bad = "\n".join(bad_lines)
        violations = cpat.lint_text(bad)
        self.assertTrue(
            any("16" in v or "field" in v.lower() for v in violations),
            msg=f"expected field-count violation; got {violations}",
        )

    def test_missing_snapshot_ref_fails(self) -> None:
        bad = _GOOD_TABLE.replace(
            "**Snapshot:** `prisma-trAIce:wayback=20260513075443` (sha256: f95fc59f…)",
            "(snapshot deleted)",
        )
        violations = cpat.lint_text(bad)
        self.assertTrue(
            any("snapshot" in v.lower() for v in violations),
            msg=f"expected snapshot-missing violation; got {violations}",
        )

    def test_mandate_cell_without_verbatim_quote_fails(self) -> None:
        # Strip the quote from ICMJE #10 (mandate cell)
        bad = _GOOD_TABLE.replace(
            '"Therefore, humans are responsible for any submitted material that '
            'included the use of AI-assisted technologies."',
            "(quote elided)",
        )
        violations = cpat.lint_text(bad)
        self.assertTrue(
            any("verbatim" in v.lower() or "quote" in v.lower() for v in violations),
            msg=f"expected verbatim-quote violation; got {violations}",
        )

    def test_unknown_source_strength_fails(self) -> None:
        bad = _GOOD_TABLE.replace("explicit-mandate", "not-a-real-strength", 1)
        violations = cpat.lint_text(bad)
        self.assertTrue(
            any("source_strength" in v.lower() or "strength" in v.lower() for v in violations),
            msg=f"expected strength-enum violation; got {violations}",
        )

    def test_invalid_anchor_slug_fails(self) -> None:
        # Add an extra anchor section with a slug not in the four canonical ones
        bad = _GOOD_TABLE + "\n\n## Anchor: fake-anchor\n\nstub\n"
        violations = cpat.lint_text(bad)
        self.assertTrue(
            any("fake-anchor" in v or "unknown" in v.lower() for v in violations),
            msg=f"expected unknown-anchor violation; got {violations}",
        )

    def test_field_out_of_order_fails(self) -> None:
        # Swap field #14 and #15 in IEEE table to test order enforcement
        bad = _GOOD_TABLE.replace(
            '| 14 | Disclosure location | explicit-mandate | "shall be disclosed',
            "## TEMP_MARKER\n",
        )
        # If we just delete a row, the field-count test catches it. To test order
        # we keep all 16 but rename one with a wrong number.
        bad = _GOOD_TABLE.replace(
            "| 14 | Disclosure location", "| 99 | Disclosure location"
        )
        violations = cpat.lint_text(bad)
        self.assertTrue(
            any("order" in v.lower() or "field" in v.lower() or "99" in v for v in violations),
            msg=f"expected ordering violation; got {violations}",
        )

    def test_duplicate_anchor_section_fails(self) -> None:
        # Codex round-3 P2 #2 closure: a second `## Anchor: ieee` heading
        # silently overwrote the first in the dict-based section split,
        # passing slug coverage. The validator now flags duplicates.
        bad = _GOOD_TABLE + "\n\n## Anchor: ieee\n\nduplicate section\n"
        violations = cpat.lint_text(bad)
        self.assertTrue(
            any("duplicate anchor section" in v for v in violations),
            msg=f"expected duplicate-section violation; got {violations}",
        )


class CheckPolicyAnchorTableNatureSourceOfTruthTest(unittest.TestCase):
    """De-dup guard: Nature anchor verbatim quotes and the v3.2 venue
    policies file both cross-reference the canonical
    shared/policy_data/nature_policy.md source pointer.
    """

    def test_nature_dedup_helper_exists(self) -> None:
        self.assertTrue(
            hasattr(cpat, "verify_nature_dedup_with_venue"),
            msg="check_policy_anchor_table.verify_nature_dedup_with_venue helper missing",
        )

    def test_nature_dedup_integration_on_real_files(self) -> None:
        anchor_path = REPO_ROOT / "academic-paper/references/policy_anchor_table.md"
        venue_path = REPO_ROOT / "academic-paper/references/venue_disclosure_policies.md"
        violations = cpat.verify_nature_dedup_with_venue(anchor_path, venue_path)
        self.assertEqual(violations, [], msg=f"dedup integration failed: {violations}")

    def test_canonical_nature_source_file_exists(self) -> None:
        # Codex round-4 P2 #4 closure: the dedup helper now confirms the
        # shared source file actually exists, not just that the path
        # string appears in both consumers.
        canonical = REPO_ROOT / "shared/policy_data/nature_policy.md"
        self.assertTrue(
            canonical.exists(),
            f"canonical Nature policy source missing at {canonical}; both "
            "consumers cite this path so the file must exist",
        )

    def test_main_command_invokes_dedup_helper(self) -> None:
        # Codex round-7 P3 #1 closure: removing the canonical Nature source
        # file should fail the main lint command (not just the unit test).
        import shutil, tempfile
        with tempfile.TemporaryDirectory() as td:
            tdir = Path(td)
            anchor = REPO_ROOT / "academic-paper/references/policy_anchor_table.md"
            venue = REPO_ROOT / "academic-paper/references/venue_disclosure_policies.md"
            # Build a working subtree mirror without the canonical Nature source
            # to confirm main() surfaces the dedup violation.
            (tdir / "academic-paper/references").mkdir(parents=True)
            (tdir / "shared/policy_data").mkdir(parents=True)
            shutil.copy(anchor, tdir / "academic-paper/references/policy_anchor_table.md")
            shutil.copy(venue, tdir / "academic-paper/references/venue_disclosure_policies.md")
            # Deliberately do NOT copy shared/policy_data/nature_policy.md
            exit_code = cpat.main(
                argv=[
                    str(tdir / "academic-paper/references/policy_anchor_table.md"),
                    "--venue-policies",
                    str(tdir / "academic-paper/references/venue_disclosure_policies.md"),
                ]
            )
            self.assertEqual(
                exit_code, 1, "main() must fail when canonical Nature source is missing"
            )


class CheckPolicyAnchorTableInvariantTest(unittest.TestCase):
    """The table must reference 16 canonical disclosure fields per anchor and
    4 canonical anchor slugs, matching the discovery doc §4.2 field list and
    §4.3-4.6 anchor inventory.
    """

    def test_canonical_anchor_slugs(self) -> None:
        self.assertEqual(
            set(cpat.CANONICAL_ANCHOR_SLUGS),
            {"prisma-trAIce", "icmje", "nature", "ieee"},
        )

    def test_canonical_field_count(self) -> None:
        self.assertEqual(cpat.CANONICAL_FIELD_COUNT, 16)


if __name__ == "__main__":
    unittest.main()
