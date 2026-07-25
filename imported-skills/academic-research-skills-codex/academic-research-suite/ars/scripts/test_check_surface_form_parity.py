"""Tests for check_surface_form_parity.py (#216).

Three layers:
  1. shipped gold set passes,
  2. mutation tests — each integrity/provenance/pair invariant goes RED when broken (non-vacuous),
  3. serializer-strip tests — render_judge_view leaks NOTHING the §F.3.6 decision keeps blind
     (the #216 decision-#2 enforcement point: framing_style / provenance_type / verdict labels /
     nested authorship signal all absent from the judge's view).
"""
from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from scripts import check_surface_form_parity as csp


def _load() -> dict:
    return json.loads(csp.DEFAULT_GOLD_SET.read_text(encoding="utf-8"))


def _manifest() -> dict | None:
    return csp._load_manifest(csp.DEFAULT_MANIFEST)


class TestShipped(unittest.TestCase):
    def test_shipped_gold_set_passes(self) -> None:
        self.assertEqual(csp.validate(_load(), _manifest()), [], msg="shipped gold set should be clean")


class TestMutations(unittest.TestCase):
    """Each test breaks ONE invariant in a deep copy and asserts a matching violation."""

    def setUp(self) -> None:
        self.data = _load()
        self.manifest = _manifest()

    def _v(self, data: dict, manifest: dict | None = ...) -> list[str]:  # type: ignore[assignment]
        return csp.validate(data, self.manifest if manifest is ... else manifest)

    def test_wrong_task_type_fails(self) -> None:
        self.data["metadata"]["task_type"] = "detector"
        self.assertTrue(any("task_type" in e for e in self._v(self.data)))

    def test_missing_judge_blind_entry_fails(self) -> None:
        self.data["metadata"]["judge_blind_fields"] = ["pair_id"]  # drop the rest
        self.assertTrue(any("judge_blind_fields missing" in e for e in self._v(self.data)))

    def test_dropping_verdict_label_from_blind_fields_fails(self) -> None:
        """codex P2: an answer-leaking label (expert_verdict / meta_reviewer_verdict /
        asymmetry_direction) dropped from judge_blind_fields must fail — else the serializer-strip
        test (which reads the same list) silently stops checking it too."""
        for leaky in ("expert_verdict", "meta_reviewer_verdict", "asymmetry_direction"):
            data = _load()
            data["metadata"]["judge_blind_fields"] = [
                f for f in data["metadata"]["judge_blind_fields"] if f != leaky
            ]
            errors = csp.validate(data, self.manifest)
            self.assertTrue(
                any("judge_blind_fields missing" in e for e in errors),
                msg=f"dropping {leaky} should fail: {errors!r}",
            )

    def test_duplicate_id_fails(self) -> None:
        self.data["items"].append(copy.deepcopy(self.data["items"][0]))
        self.assertTrue(any("duplicate id" in e for e in self._v(self.data)))

    def test_bad_framing_style_fails(self) -> None:
        self.data["items"][0]["framing_style"] = "neutral"
        self.assertTrue(any("framing_style=" in e for e in self._v(self.data)))

    def test_bad_provenance_type_fails(self) -> None:
        self.data["items"][0]["provenance_type"] = "made_up"
        self.assertTrue(any("provenance_type=" in e for e in self._v(self.data)))

    def test_bad_expected_correctness_fails(self) -> None:
        self.data["items"][0]["expected_correctness"] = "Maybe"
        self.assertTrue(any("expected_correctness=" in e for e in self._v(self.data)))

    def test_paper_verbatim_without_anchor_fails(self) -> None:
        # find a paper_verbatim item, blank its anchor
        for it in self.data["items"]:
            if it["provenance_type"] == "paper_verbatim":
                it["provenance"]["verbatim_anchor"] = ""
                break
        self.assertTrue(any("verbatim_anchor missing" in e for e in self._v(self.data)))

    def test_paper_verbatim_with_derived_from_fails(self) -> None:
        """codex P2 round 11: a maintainer marker (derived_from) on a paper_verbatim item must
        fail — a relabeled -cf rewrite must not be certified as first-party."""
        for it in self.data["items"]:
            if it["provenance_type"] == "paper_verbatim":
                it["derived_from"] = "sfp-002"
                break
        self.assertTrue(any("must NOT carry derived_from" in e for e in self._v(self.data)))

    def test_paper_verbatim_with_maintainer_source_fails(self) -> None:
        """codex P2 round 11: a paper_verbatim must have a human/ai reviewer_source, not a
        maintainer source."""
        for it in self.data["items"]:
            if it["provenance_type"] == "paper_verbatim":
                it["provenance"]["reviewer_source"] = "maintainer_rewrite"
                break
        self.assertTrue(any("must be 'human'" in e for e in self._v(self.data)))

    def test_counterfactual_claiming_verbatim_anchor_fails(self) -> None:
        """Provenance honesty (P1.5): a counterfactual must NOT carry a verbatim_anchor."""
        for it in self.data["items"]:
            if it["provenance_type"] == "counterfactual_rewrite":
                it["provenance"]["verbatim_anchor"] = "fake quote"
                break
        self.assertTrue(any("must NOT carry a verbatim_anchor" in e for e in self._v(self.data)))

    def test_counterfactual_missing_derived_from_fails(self) -> None:
        for it in self.data["items"]:
            if it["provenance_type"] == "counterfactual_rewrite":
                del it["derived_from"]
                break
        self.assertTrue(any("derived_from" in e for e in self._v(self.data)))

    def test_counterfactual_non_string_derived_from_fails(self) -> None:
        """codex P2 round 9: derived_from: null/false must fail — a str()-coerced presence check
        would pass it while the source-invariant loop skips non-strings, letting it escape."""
        for bad in (None, False, ["sfp-001"]):
            data = _load()
            for it in data["items"]:
                if it["provenance_type"] == "counterfactual_rewrite":
                    it["derived_from"] = bad
                    break
            errors = csp.validate(data, self.manifest)
            self.assertTrue(
                any("non-empty string derived_from" in e for e in errors),
                msg=f"derived_from={bad!r} should fail: {errors!r}",
            )

    def test_maintainer_boundary_missing_mechanism_anchor_fails(self) -> None:
        for it in self.data["items"]:
            if it["provenance_type"] == "maintainer_boundary":
                it["provenance"]["mechanism_anchor"] = ""
                break
        self.assertTrue(any("mechanism_anchor" in e for e in self._v(self.data)))

    def test_counterfactual_with_human_source_fails(self) -> None:
        """codex P2 round 12: a maintainer-authored counterfactual must carry maintainer_rewrite,
        not human/ai — else a synthetic rewrite gets certified source-authored."""
        for it in self.data["items"]:
            if it["provenance_type"] == "counterfactual_rewrite":
                it["provenance"]["reviewer_source"] = "human"
                break
        self.assertTrue(any("must be 'maintainer_rewrite'" in e for e in self._v(self.data)))

    def test_boundary_with_ai_source_fails(self) -> None:
        for it in self.data["items"]:
            if it["provenance_type"] == "maintainer_boundary":
                it["provenance"]["reviewer_source"] = "ai"
                break
        self.assertTrue(any("must be 'maintainer_synthetic'" in e for e in self._v(self.data)))

    def test_null_mechanism_anchor_fails(self) -> None:
        """codex P2 round 12: a null mechanism_anchor must fail — str(None) would read as present."""
        for it in self.data["items"]:
            if it["provenance_type"] == "maintainer_boundary":
                it["provenance"]["mechanism_anchor"] = None
                break
        self.assertTrue(any("non-empty string provenance.mechanism_anchor" in e for e in self._v(self.data)))

    def test_null_exception_reason_fails(self) -> None:
        """codex P2 round 12: a null exception_reason on an exception item must fail — str(None)
        would otherwise read as a present reason."""
        for it in self.data["items"]:
            if it.get("exception") is True:
                it["exception_reason"] = None
                break
        self.assertTrue(any("exception_reason missing" in e for e in self._v(self.data)))

    def test_pdftotext_line_anchor_fails(self) -> None:
        self.data["items"][0]["provenance"]["section"] = "§F.3.6 L4753"
        self.assertTrue(any("pdftotext line-number anchor" in e for e in self._v(self.data)))

    def test_pdftotext_plural_range_anchor_fails(self) -> None:
        """codex P2: the common 'lines 4753-4756' plural+range form must also be rejected."""
        self.data["items"][0]["provenance"]["section"] = "§F.3.6 lines 4753-4756"
        self.assertTrue(any("pdftotext line-number anchor" in e for e in self._v(self.data)))

    def test_paper_verbatim_anchor_not_in_review_text_fails(self) -> None:
        """codex P2: a paper_verbatim whose anchor is NOT a substring of the (possibly paraphrased)
        review_item_text must fail — otherwise maintainer text gets a paper-verbatim label."""
        for it in self.data["items"]:
            if it["provenance_type"] == "paper_verbatim":
                it["review_item_text"] = "a totally paraphrased concern with none of the quote"
                break
        self.assertTrue(
            any("not a substring of" in e for e in self._v(self.data)),
            msg=f"{self._v(self.data)!r}",
        )

    def test_pair_claim_drift_fails(self) -> None:
        """A pair whose members hold different canonical_claim must fail."""
        for it in self.data["items"]:
            if it.get("pair_id") == "pair-01" and it["id"].endswith("-cf"):
                it["canonical_claim"] = "a totally different claim"
                break
        self.assertTrue(any("different canonical_claim" in e for e in self._v(self.data)))

    def test_pair_verdict_drift_fails(self) -> None:
        """A pair whose members hold different expected_correctness must fail — framing must NOT
        change the expected verdict."""
        for it in self.data["items"]:
            if it.get("pair_id") == "pair-01" and it["id"].endswith("-cf"):
                it["expected_correctness"] = "Not Correct"
                break
        self.assertTrue(any("different expected_correctness" in e for e in self._v(self.data)))

    def test_pair_same_style_fails(self) -> None:
        """A pair whose members share framing_style is not a contrast pair."""
        for it in self.data["items"]:
            if it.get("pair_id") == "pair-01" and it["id"].endswith("-cf"):
                # set to match its partner's style
                it["framing_style"] = "informal_vague"
                break
        self.assertTrue(any("share framing_style" in e for e in self._v(self.data)))

    def test_lonely_pair_member_fails(self) -> None:
        """A pair_id with only one member must fail."""
        for it in self.data["items"]:
            if it["id"] == "sfp-001-cf":
                it["pair_id"] = None
                break
        self.assertTrue(any("must have exactly 2" in e for e in self._v(self.data)))

    def test_exception_without_reason_fails(self) -> None:
        for it in self.data["items"]:
            if it.get("exception") is True:
                it["exception_reason"] = ""
                break
        self.assertTrue(any("exception_reason missing" in e for e in self._v(self.data)))

    def test_ambiguous_id_without_flag_fails(self) -> None:
        """An id ending -ambiguous must keep exception=true, else it reverts to a clean case."""
        for it in self.data["items"]:
            if it["id"].endswith("-ambiguous"):
                it["exception"] = False
                it["exception_reason"] = ""
                break
        self.assertTrue(any("must stay marked" in e for e in self._v(self.data)))

    def test_dangling_derived_from_fails(self) -> None:
        for it in self.data["items"]:
            if it.get("derived_from"):
                it["derived_from"] = "sfp-nonexistent"
                break
        self.assertTrue(any("does not match any item id" in e for e in self._v(self.data)))

    def test_counterfactual_deriving_from_non_paper_source_fails(self) -> None:
        """codex P2: a rewrite must derive from a paper_verbatim item, not another maintainer
        item. Point a counterfactual's derived_from at the maintainer_boundary item (matching its
        claim/verdict/framing so only the provenance check can catch it)."""
        boundary = next(it for it in self.data["items"] if it["provenance_type"] == "maintainer_boundary")
        cf = next(it for it in self.data["items"] if it["provenance_type"] == "counterfactual_rewrite")
        # align claim/verdict/framing so ONLY the paper_verbatim-source check fires
        cf["derived_from"] = boundary["id"]
        cf["canonical_claim"] = boundary["canonical_claim"]
        cf["expected_correctness"] = boundary["expected_correctness"]
        cf["framing_style"] = "technical_precise" if boundary["framing_style"] == "informal_vague" else "informal_vague"
        errors = self._v(self.data)
        self.assertTrue(
            any("must derive from a paper_verbatim item" in e for e in errors),
            msg=f"non-paper derived_from should fail: {errors!r}",
        )

    def test_counterfactual_drift_caught_even_without_pair_id(self) -> None:
        """codex P2: a counterfactual that loses its pair_id (and whose manifest pair is dropped)
        must STILL be validated against its derived_from source — the pair loop would miss it, but
        the derived_from invariant check catches the claim/verdict/framing drift."""
        # drop the pair so the pair-invariant loop never runs for this rewrite...
        for it in self.data["items"]:
            if it["id"] == "sfp-001-cf":
                it["pair_id"] = None
                it["expected_correctness"] = "Not Correct"  # drift away from the source verdict
                break
        for it in self.data["items"]:
            if it["id"] == "sfp-001":
                it["pair_id"] = None
                break
        man = copy.deepcopy(self.manifest)
        man["pairs"] = [p for p in man["pairs"] if p["pair_id"] != "pair-01"]
        errors = self._v(self.data, man)
        self.assertTrue(
            any("expected_correctness differs from its derived_from" in e for e in errors),
            msg=f"drift must be caught via derived_from even without pair_id: {errors!r}",
        )

    def test_manifest_sample_n_drift_fails(self) -> None:
        man = copy.deepcopy(self.manifest)
        man["sample_n"] = 99
        self.assertTrue(any("sample_n" in e for e in self._v(self.data, man)))

    def test_manifest_provenance_dist_drift_fails(self) -> None:
        man = copy.deepcopy(self.manifest)
        man["provenance_distribution"] = [{"provenance_type": "paper_verbatim", "n": 99}]
        self.assertTrue(any("provenance_distribution" in e for e in self._v(self.data, man)))


class TestMainGuards(unittest.TestCase):
    def test_missing_manifest_makes_main_fail(self) -> None:
        """codex P2 round 7: a missing manifest must FAIL the lint, not silently skip the
        agreement checks — otherwise a deleted/renamed manifest (fixture undiscoverable by
        run_evals) passes CI."""
        rc = csp.main([str(csp.DEFAULT_GOLD_SET), "--manifest", "/tmp/does-not-exist-216.yaml"])
        self.assertEqual(rc, 1)

    def test_empty_manifest_makes_main_fail(self) -> None:
        """codex P2 round 8: a present-but-empty/null manifest must FAIL too — yaml null returns
        None and would silently disable all agreement checks (and crash run_evals later)."""
        import tempfile
        with tempfile.NamedTemporaryFile("w", suffix=".yaml", delete=False) as f:
            f.write("\n")  # empty -> yaml.safe_load returns None
            path = f.name
        rc = csp.main([str(csp.DEFAULT_GOLD_SET), "--manifest", path])
        Path(path).unlink(missing_ok=True)
        self.assertEqual(rc, 1)

    def test_non_mapping_manifest_fails_without_traceback(self) -> None:
        """codex P3 round 9: a YAML scalar/list manifest must produce a lint error (rc 1), NOT an
        AttributeError traceback from validate() calling manifest.get on a non-dict."""
        import tempfile
        with tempfile.NamedTemporaryFile("w", suffix=".yaml", delete=False) as f:
            f.write("- just\n- a\n- list\n")  # YAML list -> non-dict
            path = f.name
        try:
            rc = csp.main([str(csp.DEFAULT_GOLD_SET), "--manifest", path])  # must not raise
        finally:
            Path(path).unlink(missing_ok=True)
        self.assertEqual(rc, 1)

    def test_shipped_main_passes(self) -> None:
        self.assertEqual(csp.main([str(csp.DEFAULT_GOLD_SET)]), 0)


class TestSerializerStrip(unittest.TestCase):
    """The #216 decision-#2 enforcement point: render_judge_view must leak NOTHING blind."""

    def setUp(self) -> None:
        self.items = _load()["items"]

    def test_judge_view_only_whitelisted_keys(self) -> None:
        allowed = {"handle", csp.JUDGE_VISIBLE_CONTENT_KEY}
        for i, it in enumerate(self.items):
            view = csp.render_judge_view(it, i)
            self.assertEqual(
                set(view.keys()) - allowed,
                set(),
                msg=f"judge view for {it['id']} leaked non-whitelisted keys: {view.keys()}",
            )

    def test_judge_view_strips_all_blind_fields(self) -> None:
        blind = set(_load()["metadata"]["judge_blind_fields"])
        for i, it in enumerate(self.items):
            view = csp.render_judge_view(it, i)
            leaked = blind & set(view.keys())
            self.assertEqual(leaked, set(), msg=f"judge view for {it['id']} leaked blind fields: {leaked}")

    def test_judge_view_does_not_leak_semantic_id(self) -> None:
        """The fixture id encodes the answer (`-cf` = counterfactual, `-ambiguous` = expected
        boundary verdict). It must NOT appear in the judge view — the handle is DERIVED INTERNALLY
        from the index, so even the caller cannot inject the id. (codex review P2.)"""
        for i, it in enumerate(self.items):
            view = csp.render_judge_view(it, i)
            serialized = json.dumps(view)
            self.assertNotIn(it["id"], serialized, msg=f"{it['id']}: semantic id leaked into judge view")
            for suffix in ("-cf", "-ambiguous"):
                self.assertNotIn(suffix, serialized, msg=f"{it['id']}: leaked id suffix {suffix}")
            # the handle is opaque and derived from the index, NOT caller-controlled
            self.assertEqual(view["handle"], f"item-{i}")

    def test_judge_view_rejects_non_int_index(self) -> None:
        """codex P2 round 10: a string/bool index would be interpolated into the handle and leak
        an answer-encoding suffix. The helper must raise (a runtime check, not an -O-stripped
        assert) instead of producing a leaky handle."""
        sample = self.items[0]
        for bad in ("sfp-001-cf", "pair-01", True, 1.0):
            with self.assertRaises(TypeError, msg=f"index={bad!r} should raise"):
                csp.render_judge_view(sample, bad)

    def test_judge_handle_is_index_derived_not_caller_controlled(self) -> None:
        """The helper derives the handle from the index; it does not accept an arbitrary string.
        Passing an int index always yields item-<index>, so a caller cannot smuggle the fixture
        id in as the handle (the codex-P2 leak path is closed at the API level)."""
        sample = self.items[0]
        self.assertEqual(csp.render_judge_view(sample, 3)["handle"], "item-3")
        # the answer-encoding id is never echoed regardless of which item is rendered
        for i, it in enumerate(self.items):
            if it["id"].endswith(("-cf", "-ambiguous")):
                self.assertNotIn(it["id"], json.dumps(csp.render_judge_view(it, i)))

    def test_judge_view_strips_nested_authorship_signal(self) -> None:
        """The nested provenance.reviewer_source (human/ai/maintainer_rewrite) is the author
        label §F.3.6 is built to hide. It must not appear anywhere in the serialized view."""
        for i, it in enumerate(self.items):
            view = csp.render_judge_view(it, i)
            serialized = json.dumps(view)
            self.assertNotIn("reviewer_source", serialized, msg=f"{it['id']}: leaked reviewer_source")
            for label in ("\"human\"", "\"ai\"", "maintainer_rewrite", "maintainer_synthetic"):
                self.assertNotIn(label, serialized, msg=f"{it['id']}: leaked author label {label}")

    def test_judge_view_keeps_the_item_to_judge(self) -> None:
        """Strip must not be so aggressive it removes the thing being evaluated."""
        for i, it in enumerate(self.items):
            view = csp.render_judge_view(it, i)
            self.assertIn("review_item_text", view, msg=f"{it['id']}: judge view lost review_item_text")
            self.assertTrue(view["review_item_text"].strip())


if __name__ == "__main__":
    unittest.main()
