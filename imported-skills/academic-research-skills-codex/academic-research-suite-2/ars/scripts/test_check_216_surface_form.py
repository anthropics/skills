"""Mutation tests for check_216_surface_form.py (#216).

The lint reads the real Devil's Advocate agent surface. These tests (a) assert the shipped
file passes, and (b) monkey-patch the file reader to inject mutated content so every assertion
is shown non-vacuous: the lint goes RED when a marker, a load-bearing clause, the verdict-time
framing, the §F.3.6 attribution, or the epistemic disclaimer is removed / weakened / de-scoped.

Covers the six mutation classes codex flagged (P1.2):
  1. clause deletion           -> test_clause_*_removed_fails
  2. MUST/SHOULD weakening      -> test_authorship_softened_fails / test_down_rate_softened_fails
  3. marker-only block          -> test_block_emptied_of_clauses_fails
  4. clause moved outside block -> test_clause_moved_outside_block_fails
  5. fenced-marker truncation   -> test_markers_fenced_fails
  6. verdict/output-surface     -> test_verdict_framing_removed_fails
"""
from __future__ import annotations

import unittest

from scripts import check_216_surface_form as csf

DA = csf.DA_AGENT


class TestShipped(unittest.TestCase):
    def test_shipped_surface_passes(self) -> None:
        self.assertEqual(csf.check(), [], msg="shipped DA surface should pass #216 lint")


class TestMutations(unittest.TestCase):
    def setUp(self) -> None:
        self._orig_read = csf._read
        self._real = csf._read(DA)

    def tearDown(self) -> None:
        csf._read = self._orig_read

    def _patch(self, mutate) -> list[str]:
        mutated = mutate(self._real)
        csf._read = lambda p: mutated if p == DA else self._orig_read(p)
        return csf.check()

    # --- 1. clause deletion (one test per load-bearing clause, proving each is non-vacuous) ---

    def test_clause_extract_substance_removed_fails(self) -> None:
        errors = self._patch(lambda t: t.replace("Extract the checkable substance first", "Skip the substance"))
        self.assertTrue(any("extract-substance" in e for e in errors), msg=f"{errors!r}")

    def test_clause_judge_vs_paper_removed_fails(self) -> None:
        errors = self._patch(
            lambda t: t.replace("Judge the claim against the paper, not against the polish", "Judge however")
        )
        self.assertTrue(any("judge-vs-paper-not-polish" in e for e in errors), msg=f"{errors!r}")

    def test_clause_no_credit_specificity_removed_fails(self) -> None:
        errors = self._patch(lambda t: t.replace("Do not credit technical specificity", "Credit specificity"))
        self.assertTrue(any("no-credit-specificity" in e for e in errors), msg=f"{errors!r}")

    def test_clause_checking_required_removed_fails(self) -> None:
        errors = self._patch(
            lambda t: t.replace("still requires checking against the paper before you accept it", "is fine to accept")
        )
        self.assertTrue(any("still-requires-checking" in e for e in errors), msg=f"{errors!r}")

    def test_clause_counterfactual_removed_fails(self) -> None:
        errors = self._patch(lambda t: t.replace("Run the opposite-style counterfactual", "Skip the counterfactual"))
        self.assertTrue(any("opposite-style-counterfactual" in e for e in errors), msg=f"{errors!r}")

    def test_clause_would_verdict_change_removed_fails(self) -> None:
        errors = self._patch(
            lambda t: t.replace(
                "would my verdict change if this same substantive claim were rewritten in the opposite style",
                "nothing changes",
            )
        )
        self.assertTrue(any("would-my-verdict-change" in e for e in errors), msg=f"{errors!r}")

    def test_clause_revise_or_ambiguous_removed_fails(self) -> None:
        errors = self._patch(
            lambda t: t.replace("revise the verdict, or mark the claim ambiguous", "keep the verdict")
        )
        self.assertTrue(any("revise-or-mark-ambiguous" in e for e in errors), msg=f"{errors!r}")

    # --- 2. MUST/SHOULD-style weakening (the guard binds the modal to the action) ---

    def test_authorship_softened_fails(self) -> None:
        """Flipping the deliberate 'not a judgment input' to allow authorship must fail."""
        errors = self._patch(
            lambda t: t.replace(
                "Authorship (human vs AI origin of a concern) is deliberately **not** a judgment input",
                "Authorship may be considered as a judgment input",
            )
        )
        self.assertTrue(any("authorship-not-input" in e for e in errors), msg=f"{errors!r}")

    def test_down_rate_softened_fails(self) -> None:
        """Weakening 'Do not down-rate informal or vague wording' must fail — a bare 'down-rate'
        elsewhere cannot satisfy the bound clause."""
        errors = self._patch(
            lambda t: t.replace("Do not down-rate informal or vague wording", "You may down-rate informal wording")
        )
        self.assertTrue(any("no-down-rate-informal" in e for e in errors), msg=f"{errors!r}")

    def test_unless_guard_removed_fails(self) -> None:
        """Dropping the UNLESS guard turns the parity rule into 'never penalise vagueness',
        which would over-correct (the sfp-005 boundary). Must fail."""
        errors = self._patch(
            lambda t: t.replace(
                "unless* the ambiguity actually changes the truth conditions or makes the claim unevaluable",
                "no matter what",
            )
        )
        self.assertTrue(any("unless-truth-conditions" in e for e in errors), msg=f"{errors!r}")

    # --- 3. marker-only block (markers present but all clauses gone) ---

    def test_block_emptied_of_clauses_fails(self) -> None:
        """Keep the BEGIN/END markers but replace the clause body with filler. A marker-presence
        check would false-pass; the clause checks must fail."""
        block = csf._marker_block(self._real)
        assert block is not None
        errors = self._patch(lambda t: t.replace(block, "\nSee elsewhere for details.\n"))
        self.assertTrue(
            sum("parity block: missing load-bearing clause" in e for e in errors) >= 5,
            msg=f"emptied block should drop many clauses: {errors!r}",
        )

    # --- 4. clause moved outside the marker block (block-scoping proof) ---

    def test_clause_moved_outside_block_fails(self) -> None:
        """Delete a clause from inside the block and re-add it AFTER the END marker. The clause
        text still exists in the file, but the block-scoped check must still fail — proving the
        lint is block-scoped, not file-wide."""
        needle = "Run the opposite-style counterfactual."

        def mutate(t: str) -> str:
            t2 = t.replace("- **Run the opposite-style counterfactual.**", "- (moved)")
            # re-inject the raw clause text after the END marker, outside the block
            return t2.replace(csf.END_MARKER + " (#216) -->", csf.END_MARKER + " (#216) -->\n" + needle)

        errors = self._patch(mutate)
        self.assertTrue(any("opposite-style-counterfactual" in e for e in errors), msg=f"{errors!r}")

    def test_marker_block_moved_out_of_section_fails(self) -> None:
        """codex P2: if the whole marker block is relocated to AFTER the parity section ends
        (e.g. into Severity Classification) while the section header/framing/disclaimer remain,
        a file-wide marker lookup would false-pass. The section-scoped lookup must fail."""
        begin = "<!-- " + csf.BEGIN_MARKER
        end_tail = csf.END_MARKER + " (#216) -->"

        def mutate(t: str) -> str:
            b = t.index(begin)
            e = t.index(end_tail, b) + len(end_tail)
            block = t[b:e]
            without = t[:b] + "(parity steps moved below)\n" + t[e:]
            # re-inject the block INSIDE a later section (after the Severity Classification header)
            # so it is out of the parity section but still present in the file.
            anchor = "## Severity Classification\n"
            return without.replace(anchor, anchor + "\n" + block + "\n\n", 1)

        errors = self._patch(mutate)
        self.assertTrue(
            any("INSIDE the" in e and "section" in e and DA in e for e in errors),
            msg=f"out-of-section marker should fail: {errors!r}",
        )

    def test_whole_section_fenced_fails(self) -> None:
        """codex P2 round 8: if the ENTIRE parity section (header included) is wrapped in a ```
        fence, the header match must be ignored (it is only a code sample). The lint must report
        the section as missing, not pass on a fenced sample."""
        header = "## Surface-Form Parity Self-Check (#216)"

        def mutate(t: str) -> str:
            idx = t.index(header)
            # wrap from the header through the end of the section's epistemic disclaimer in a fence
            end_anchor = "## Severity Classification"
            end = t.index(end_anchor, idx)
            return t[:idx] + "```\n" + t[idx:end] + "```\n\n" + t[end:]

        errors = self._patch(mutate)
        self.assertTrue(
            any(DA in e and "missing" in e and "section" in e for e in errors),
            msg=f"fenced section should be treated as missing: {errors!r}",
        )

    # --- 5. fenced-marker truncation (markers buried in a code fence are not live) ---

    def test_markers_fenced_fails(self) -> None:
        """Wrap the whole marker block in a ``` fence. The markers then sit inside a code sample
        and must not count as a live block."""

        def mutate(t: str) -> str:
            block_full_begin = "<!-- " + csf.BEGIN_MARKER
            idx = t.index(block_full_begin)
            return t[:idx] + "```\n" + t[idx:].replace(
                csf.END_MARKER + " (#216) -->", csf.END_MARKER + " (#216) -->\n```", 1
            )

        errors = self._patch(mutate)
        self.assertTrue(
            any("marker block" in e for e in errors),
            msg=f"fenced markers should not count as a live block: {errors!r}",
        )

    def test_clauses_fenced_inside_block_fails(self) -> None:
        """codex P2 round 12: markers stay live but the bullet clauses between them are wrapped in
        a ``` fence. The clauses are then only a sample; the live-text check must fail."""
        block = csf._marker_block(self._real)
        assert block is not None
        errors = self._patch(lambda t: t.replace(block, "\n```\n" + block + "\n```\n"))
        self.assertTrue(
            sum("missing load-bearing clause" in e for e in errors) >= 5,
            msg=f"fenced clauses should not count as live: {errors!r}",
        )

    # --- 6. verdict/output-surface framing removal ---

    def test_verdict_framing_removed_fails(self) -> None:
        errors = self._patch(
            lambda t: t.replace("verdict-assignment time", "some time").replace("verdict time", "some time")
        )
        self.assertTrue(any("verdict" in e and "time-of-application" in e for e in errors), msg=f"{errors!r}")

    def test_section_header_removed_fails(self) -> None:
        errors = self._patch(
            lambda t: t.replace("## Surface-Form Parity Self-Check (#216)", "## Removed Section")
        )
        self.assertTrue(any("missing '## Surface-Form Parity Self-Check (#216)' section" in e for e in errors), msg=f"{errors!r}")

    def test_f36_attribution_removed_fails(self) -> None:
        errors = self._patch(lambda t: t.replace("§F.3.6", "§X"))
        self.assertTrue(any("§F.3.6 paper attribution" in e for e in errors), msg=f"{errors!r}")

    def test_epistemic_disclaimer_removed_fails(self) -> None:
        errors = self._patch(lambda t: t.replace("Epistemic status", "Note"))
        self.assertTrue(any("epistemic-status disclaimer" in e for e in errors), msg=f"{errors!r}")


SYNTH = csf.SYNTH_AGENT


class TestSynthesizerSurface(unittest.TestCase):
    """The editorial synthesizer is the SECOND verdict-time surface (codex P2 round 6). It must
    carry its own scoped parity block; each assertion is proven non-vacuous by a mutation."""

    def setUp(self) -> None:
        self._orig_read = csf._read
        self._real = csf._read(SYNTH)

    def tearDown(self) -> None:
        csf._read = self._orig_read

    def _patch(self, mutate) -> list[str]:
        mutated = mutate(self._real)
        csf._read = lambda p: mutated if p == SYNTH else self._orig_read(p)
        return csf.check()

    def test_synth_section_present_in_shipped(self) -> None:
        # sanity: the shipped synthesizer passes (no patch)
        csf._read = self._orig_read
        self.assertEqual(csf.check(), [], msg="shipped surfaces should pass")

    def test_synth_section_removed_fails(self) -> None:
        errors = self._patch(lambda t: t.replace("### Step 1c — Surface-Form Parity Check (#216)", "### Step 1c — Removed"))
        self.assertTrue(any(SYNTH in e and "missing" in e and "section" in e for e in errors), msg=f"{errors!r}")

    def test_synth_clause_no_down_rate_removed_fails(self) -> None:
        errors = self._patch(lambda t: t.replace("Do not down-rate informal or vague wording", "You may down-rate"))
        self.assertTrue(any(SYNTH in e and "no-down-rate-informal" in e for e in errors), msg=f"{errors!r}")

    def test_synth_clause_authorship_removed_fails(self) -> None:
        errors = self._patch(
            lambda t: t.replace(
                "Authorship (whether a sub-claim originated from a human or an AI reviewer) is **not** a weighting input",
                "Authorship may weight a sub-claim",
            )
        )
        self.assertTrue(any(SYNTH in e and "authorship-not-input" in e for e in errors), msg=f"{errors!r}")

    def test_synth_clause_reweight_unevaluable_removed_fails(self) -> None:
        errors = self._patch(
            lambda t: t.replace("re-weight on substance, or mark the sub-claim unevaluable", "keep the weight")
        )
        self.assertTrue(any(SYNTH in e and "reweight-or-unevaluable" in e for e in errors), msg=f"{errors!r}")

    def test_synth_marker_block_removed_fails(self) -> None:
        block = csf._marker_block(self._real)
        assert block is not None
        errors = self._patch(lambda t: t.replace(block, "\nsee elsewhere\n"))
        self.assertTrue(
            sum(SYNTH in e and "missing load-bearing clause" in e for e in errors) >= 4,
            msg=f"emptied synth block should drop clauses: {errors!r}",
        )

    def test_synth_f36_attribution_removed_fails(self) -> None:
        errors = self._patch(lambda t: t.replace("§F.3.6", "§X"))
        self.assertTrue(any(SYNTH in e and "§F.3.6 paper attribution" in e for e in errors), msg=f"{errors!r}")

    def test_synth_marker_moved_to_later_subsection_fails(self) -> None:
        """codex P2 round 7: Step 1c is a ### section, so _section() must stop at the next ###
        (Step 2), not only at ##. Move the marker block out of Step 1c into Step 2; the
        section-scoped check must fail because the block is no longer inside Step 1c."""
        begin = "<!-- " + csf.BEGIN_MARKER
        end_tail = csf.END_MARKER + " (#216) -->"

        def mutate(t: str) -> str:
            b = t.index(begin)
            e = t.index(end_tail, b) + len(end_tail)
            block = t[b:e]
            without = t[:b] + "(parity steps moved below)\n" + t[e:]
            # re-inject INSIDE the later ### Step 2 subsection
            anchor = "### Step 2: Consensus Identification\n"
            return without.replace(anchor, anchor + "\n" + block + "\n\n", 1)

        errors = self._patch(mutate)
        self.assertTrue(
            any(SYNTH in e and "INSIDE the" in e and "section" in e for e in errors),
            msg=f"block moved to a later ### should fail: {errors!r}",
        )


if __name__ == "__main__":
    unittest.main()
