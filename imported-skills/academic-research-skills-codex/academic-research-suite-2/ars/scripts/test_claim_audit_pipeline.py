"""Audit-pipeline unit tests for v3.8 claim_ref_alignment_audit_agent (T-P1..T-P11).

Per spec §7.2 in
docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md.

These tests pin the contract of `scripts/claim_audit_pipeline.py`, the
Python module that implements the §4 Step 1-6 pipeline the agent prompt
narrates. Retrieval and judge are dependency-injected so tests can drive
every error path (paywall, audit_tool_failure, not_found, VIOLATED, etc.)
without touching the network or the on-disk cache.

Spec §7 names the test file `tests/test_claim_audit_pipeline.py`. Per
repo convention, tests live under `scripts/test_*.py` (CI uses
`python -m unittest scripts.test_*`); we keep the spec-named stem.

Run:
    python -m unittest scripts.test_claim_audit_pipeline -v
"""
from __future__ import annotations

import unittest
from pathlib import Path
from typing import Any, Callable
from unittest import mock

from tests.test_helpers import build_schema_validator, load_json_schema

try:
    from scripts.claim_audit_pipeline import run_audit_pipeline  # noqa: F401
    _MODULE_IMPORT_ERR: Exception | None = None
except Exception as exc:  # pragma: no cover — import-time error pathway is exercised in RED state
    _MODULE_IMPORT_ERR = exc

    def run_audit_pipeline(*args: Any, **kwargs: Any) -> Any:
        raise _MODULE_IMPORT_ERR  # type: ignore[misc]


# claim_audit_result schema validator — an emitted row MUST satisfy the
# passport entry schema (incl. rationale maxLength=2000). Some failure paths
# build the rationale from untrusted judge output, so a row that is supposed to
# be a clean inconclusive fallback can still overflow the schema (#355 P2#3).
_CAR_SCHEMA = load_json_schema(
    Path(__file__).resolve().parent.parent / "shared/contracts/passport/claim_audit_result.schema.json"
)
_CAR_VALIDATOR = build_schema_validator(_CAR_SCHEMA)

# constraint_violation schema validator — a VIOLATED uncited claim rides in its
# own aggregate (rationale maxLength=2000 too). Its rationale is also copied
# straight from untrusted judge output on the success path (#360), so the same
# overflow can land a schema-invalid constraint_violation row.
_CV_SCHEMA = load_json_schema(
    Path(__file__).resolve().parent.parent / "shared/contracts/passport/constraint_violation.schema.json"
)
_CV_VALIDATOR = build_schema_validator(_CV_SCHEMA)


MANIFEST_ID = "M-2026-05-15T10:00:00Z-a1b2"
MANIFEST_ID_OTHER = "M-2026-05-15T10:05:00Z-c3d4"
AUDIT_RUN_ID = "2026-05-15T10:10:00Z-9f8e"
NOW = "2026-05-15T10:11:00Z"


def _manifest(
    *,
    claims: list[dict[str, Any]] | None = None,
    mncs: list[dict[str, str]] | None = None,
    manifest_id: str = MANIFEST_ID,
) -> dict[str, Any]:
    return {
        "manifest_version": "1.0",
        "manifest_id": manifest_id,
        "emitted_by": "synthesis_agent",
        "emitted_at": "2026-05-15T09:55:00Z",
        "claims": claims
        if claims is not None
        else [
            {
                "claim_id": "C-001",
                "claim_text": "Sample preprints accounted for 67% of corpus.",
                "intended_evidence_kind": "empirical",
                "planned_refs": ["smith2024preprints"],
            }
        ],
        "manifest_negative_constraints": mncs or [],
    }


def _citation(
    *,
    claim_id: str = "C-001",
    claim_text: str = "Sample preprints accounted for 67% of corpus.",
    ref_slug: str = "smith2024preprints",
    anchor_kind: str = "page",
    anchor_value: str = "12",
    section_path: str = "3. Results > 3.1 Overview",
    scoped_manifest_id: str = MANIFEST_ID,
) -> dict[str, Any]:
    return {
        "claim_id": claim_id,
        "scoped_manifest_id": scoped_manifest_id,
        "claim_text": claim_text,
        "ref_slug": ref_slug,
        "anchor_kind": anchor_kind,
        "anchor_value": anchor_value,
        "section_path": section_path,
    }


def _config(**overrides: Any) -> dict[str, Any]:
    base: dict[str, Any] = {
        "max_claims_per_paper": 100,
        "judge_model": "gpt-5.5-xhigh",
        "gold_set_path": None,
        "cache_dir": None,  # Inject in-memory cache via run_audit_pipeline kwargs.
    }
    base.update(overrides)
    return base


def _retrieval_ok(
    *,
    excerpt: str = "The cited page reports the 67% figure verbatim.",
) -> Callable[[dict[str, Any]], dict[str, Any]]:
    def fn(citation: dict[str, Any]) -> dict[str, Any]:
        return {
            "ref_retrieval_method": "api",
            "retrieved_excerpt": excerpt,
        }

    return fn


def _judge_supported() -> Callable[..., dict[str, Any]]:
    def fn(**kwargs: Any) -> dict[str, Any]:
        return {
            "judgment": "SUPPORTED",
            "rationale": "Cited page contains the 67% figure verbatim.",
        }

    return fn


def _judge_unsupported(*, defect_stage: str = "source_description") -> Callable[..., dict[str, Any]]:
    def fn(**kwargs: Any) -> dict[str, Any]:
        return {
            "judgment": "UNSUPPORTED",
            "rationale": f"Source describes a different population than the claim asserts.",
            "defect_stage_hint": defect_stage,
        }

    return fn


def _judge_violated(*, violated_constraint_id: str) -> Callable[..., dict[str, Any]]:
    def fn(**kwargs: Any) -> dict[str, Any]:
        return {
            "judgment": "VIOLATED",
            "violated_constraint_id": violated_constraint_id,
            "rationale": "Constraint forbids unqualified causal language.",
        }

    return fn


def _judge_partial(
    *, breakdown: list[dict[str, Any]] | None = None
) -> Callable[..., dict[str, Any]]:
    """#213: a judge that returns a well-formed PARTIAL with a true-partial breakdown."""
    def fn(**kwargs: Any) -> dict[str, Any]:
        return {
            "judgment": "PARTIAL",
            "rationale": "Reference supports the first sub-claim but not the second.",
            "sub_claim_breakdown": breakdown
            if breakdown is not None
            else [
                {"sub_claim_text": "preprints are 67%", "sub_verdict": "SUPPORTED", "evidence_pointer": "p.12"},
                {"sub_claim_text": "trend held across venues", "sub_verdict": "UNSUPPORTED", "evidence_pointer": None},
            ],
        }

    return fn


def _judge_partial_malformed(
    *, breakdown: Any
) -> Callable[..., dict[str, Any]]:
    """#213: a judge that returns PARTIAL with a malformed (not true-partial) breakdown."""
    def fn(**kwargs: Any) -> dict[str, Any]:
        return {"judgment": "PARTIAL", "rationale": "partial but malformed", "sub_claim_breakdown": breakdown}

    return fn


class _PipelineTestBase(unittest.TestCase):
    """Skip the entire pipeline suite cleanly when the module is missing.

    During the RED phase (Step 4 of the TDD plan in spec §13), the module
    `scripts/claim_audit_pipeline.py` does not exist yet — these tests
    document the wished-for API. Once Step 5 lands the module, they will
    flip from skipped (RED-as-skip) to executed pass/fail.
    """

    @classmethod
    def setUpClass(cls) -> None:
        if _MODULE_IMPORT_ERR is not None:
            raise unittest.SkipTest(
                f"scripts.claim_audit_pipeline not importable yet: {_MODULE_IMPORT_ERR!r} "
                "(expected during RED phase — implementation lands in spec §13 step 5)"
            )

    def run_pipeline(self, **kwargs: Any) -> dict[str, list[dict[str, Any]]]:
        defaults: dict[str, Any] = {
            "manifests": [_manifest()],
            "corpus": [],
            "config": _config(),
            "audit_run_id": AUDIT_RUN_ID,
            "now_iso": NOW,
            "retrieve_fn": _retrieval_ok(),
            "judge_fn": _judge_supported(),
        }
        defaults.update(kwargs)
        return run_audit_pipeline(**defaults)

    def _validate_passport(
        self, out: dict[str, Any], manifests: list[dict[str, Any]] | None = None
    ) -> list[Any]:
        from scripts.check_claim_audit_consistency import validate_passport

        body = {
            "claim_intent_manifests": manifests if manifests is not None else [_manifest()],
            "claim_audit_results": out["claim_audit_results"],
            "uncited_assertions": out.get("uncited_assertions", []),
            "claim_drifts": out.get("claim_drifts", []),
            "constraint_violations": out.get("constraint_violations", []),
            "audit_sampling_summaries": out.get("audit_sampling_summaries", []),
            "uncited_audit_failures": out.get("uncited_audit_failures", []),
        }
        return validate_passport(body)


# ---------------------------------------------------------------------------
# T-P1 — Step 1 anchor=none short-circuit.
# ---------------------------------------------------------------------------


class TP1AnchorNoneShortCircuit(_PipelineTestBase):
    """T-P1: anchor=none input emits the canonical RETRIEVAL_FAILED triple and skips the judge."""

    def test_anchor_none_skips_judge(self) -> None:
        invocations: list[Any] = []

        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            invocations.append(kwargs)
            return {"judgment": "SUPPORTED", "rationale": "should not be called"}

        out = self.run_pipeline(
            citations=[_citation(anchor_kind="none", anchor_value="")],
            judge_fn=judge_fn,
        )
        self.assertEqual(invocations, [], "judge MUST NOT be invoked for anchor=none rows")
        results = out["claim_audit_results"]
        self.assertEqual(len(results), 1)
        e = results[0]
        self.assertEqual(e["judgment"], "RETRIEVAL_FAILED")
        self.assertEqual(e["audit_status"], "inconclusive")
        self.assertEqual(e["defect_stage"], "not_applicable")
        self.assertEqual(e["ref_retrieval_method"], "not_attempted")
        self.assertTrue(
            e["rationale"].startswith("v3.7.3 R-L3-1-A violation"),
            f"rationale must start with INV-6 firm-rule prefix; got {e['rationale']!r}",
        )

    def test_anchor_none_pins_empty_sentinel_anchor_value(self) -> None:
        # INV-6 sentinel: even if the caller passes a stale residual anchor_value
        # on an anchor_kind=none citation, the pipeline MUST coerce it to the
        # empty string per the schema contract (Step 13 R1 Gemini finding).
        out = self.run_pipeline(
            citations=[_citation(anchor_kind="none", anchor_value="123")],
            judge_fn=lambda **_kw: {"judgment": "SUPPORTED", "rationale": "n/a"},
        )
        results = out["claim_audit_results"]
        self.assertEqual(len(results), 1)
        self.assertEqual(
            results[0]["anchor_value"],
            "",
            "anchor_kind=none rows must carry the empty sentinel anchor_value per INV-6",
        )


# ---------------------------------------------------------------------------
# T-P2 / T-P3 — Step 3 cache hit / miss.
# ---------------------------------------------------------------------------


class TP2P3CacheBehavior(_PipelineTestBase):
    """T-P2/T-P3: cache keyed by (claim, ref, anchor, retrieved_excerpt_hash, constraint_set, judge_model)."""

    def test_p2_cache_hit_skips_judge(self) -> None:
        cache: dict[str, Any] = {}
        invocations: list[Any] = []

        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            invocations.append(kwargs)
            return {"judgment": "SUPPORTED", "rationale": "judge ran"}

        # First run populates the cache.
        self.run_pipeline(
            citations=[_citation()],
            judge_fn=judge_fn,
            cache=cache,
        )
        self.assertEqual(len(invocations), 1, "first run must invoke judge")

        # Second run with same inputs MUST hit cache.
        self.run_pipeline(
            citations=[_citation()],
            judge_fn=judge_fn,
            cache=cache,
        )
        self.assertEqual(len(invocations), 1, "second run with identical inputs must NOT re-invoke judge")

    def test_p3_cache_miss_after_manual_pdf_uploaded(self) -> None:
        cache: dict[str, Any] = {}
        invocations: list[Any] = []

        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            invocations.append(kwargs)
            return {"judgment": "SUPPORTED", "rationale": "judge ran"}

        # First run with API retrieval.
        self.run_pipeline(
            citations=[_citation()],
            judge_fn=judge_fn,
            retrieve_fn=_retrieval_ok(excerpt="api-served excerpt"),
            cache=cache,
        )
        # Second run with manual_pdf uploading a different excerpt -> retrieved_excerpt_hash changes
        # -> cache MUST miss and re-invoke the judge.

        def manual_pdf_retrieval(citation: dict[str, Any]) -> dict[str, Any]:
            return {
                "ref_retrieval_method": "manual_pdf",
                "retrieved_excerpt": "different excerpt from manual PDF upload",
            }

        self.run_pipeline(
            citations=[_citation()],
            judge_fn=judge_fn,
            retrieve_fn=manual_pdf_retrieval,
            cache=cache,
        )
        self.assertEqual(
            len(invocations),
            2,
            "manual PDF excerpt with different hash MUST force a fresh judge invocation",
        )


# ---------------------------------------------------------------------------
# #361 — prompt-version partitions the judge cache keyspace.
# ---------------------------------------------------------------------------


class TP361PromptVersionCacheKey(_PipelineTestBase):
    """#361: the judge cache key must include a prompt-version component so a
    judge-prompt revision (e.g. #213 Step-0 decomposition) invalidates stale
    entries automatically — a verdict cached under prompt A must NOT be served
    once the active prompt is B. Same-version entries still dedup (no
    regression). When no concrete prompt version can be resolved (caller
    declares it unknown), the cache fails CLOSED — stale entries are never
    served across an unknown-version boundary.
    """

    @staticmethod
    def _counting_judge(invocations: list[Any]) -> Callable[..., dict[str, Any]]:
        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            invocations.append(kwargs)
            return {"judgment": "SUPPORTED", "rationale": "judge ran"}

        return judge_fn

    def test_prompt_version_change_misses_cache(self) -> None:
        cache: dict[str, Any] = {}
        invocations: list[Any] = []
        judge_fn = self._counting_judge(invocations)

        # Populate under prompt version A.
        self.run_pipeline(
            citations=[_citation()],
            judge_fn=judge_fn,
            cache=cache,
            config=_config(judge_prompt_version="promptA"),
        )
        self.assertEqual(len(invocations), 1, "first run must invoke judge")

        # Same (claim, ref, anchor, excerpt, constraints, model) but a NEW
        # prompt version MUST miss and re-invoke the judge.
        self.run_pipeline(
            citations=[_citation()],
            judge_fn=judge_fn,
            cache=cache,
            config=_config(judge_prompt_version="promptB"),
        )
        self.assertEqual(
            len(invocations), 2,
            "a prompt-version change MUST invalidate the stale entry and re-invoke the judge",
        )

    def test_same_prompt_version_still_hits(self) -> None:
        # Regression guard: identical prompt version keeps the existing dedup.
        cache: dict[str, Any] = {}
        invocations: list[Any] = []
        judge_fn = self._counting_judge(invocations)

        for _ in range(2):
            self.run_pipeline(
                citations=[_citation()],
                judge_fn=judge_fn,
                cache=cache,
                config=_config(judge_prompt_version="promptA"),
            )
        self.assertEqual(
            len(invocations), 1,
            "two runs under the same prompt version must hit the cache (no dedup regression)",
        )

    def test_unknown_prompt_version_fails_closed(self) -> None:
        # Caller declares the prompt version unknown (None). Across two distinct
        # runs (different audit_run_id) the cache must NOT serve the stale entry
        # — the unknown version binds a run-local component, so each run misses.
        cache: dict[str, Any] = {}
        invocations: list[Any] = []
        judge_fn = self._counting_judge(invocations)

        for run_id in ("2026-05-15T10:10:00Z-run1", "2026-05-15T10:20:00Z-run2"):
            self.run_pipeline(
                citations=[_citation()],
                judge_fn=judge_fn,
                cache=cache,
                config=_config(judge_prompt_version=None),
                audit_run_id=run_id,
            )
        self.assertEqual(
            len(invocations), 2,
            "an unknown prompt version must fail closed — no cross-run cache hit",
        )

    def test_unknown_prompt_version_dedups_within_a_run(self) -> None:
        # Fail-closed must not break WITHIN-run dedup: two identical citations in
        # the SAME run (same audit_run_id) share the run-local component, so the
        # second is a hit — the judge runs once.
        cache: dict[str, Any] = {}
        invocations: list[Any] = []
        judge_fn = self._counting_judge(invocations)

        self.run_pipeline(
            citations=[_citation(), _citation()],
            judge_fn=judge_fn,
            cache=cache,
            config=_config(judge_prompt_version=None),
        )
        self.assertEqual(
            len(invocations), 1,
            "two identical citations in one run must still dedup under the run-local key",
        )

    def test_default_prompt_version_hits_across_runs(self) -> None:
        # When the caller does NOT declare a version at all, the repo constant
        # JUDGE_PROMPT_VERSION supplies a real version → normal dedup holds.
        cache: dict[str, Any] = {}
        invocations: list[Any] = []
        judge_fn = self._counting_judge(invocations)

        for _ in range(2):
            self.run_pipeline(citations=[_citation()], judge_fn=judge_fn, cache=cache)
        self.assertEqual(
            len(invocations), 1,
            "absent an explicit version, the repo constant is a real version and dedup holds",
        )

    def test_default_tracks_prompt_hash_not_version_label(self) -> None:
        # codex P2: with NO explicit judge_prompt_version, the default cache-key
        # prompt component must be the prompt FINGERPRINT (JUDGE_PROMPT_SHA256),
        # not the decoupled human-readable JUDGE_PROMPT_VERSION label. A prompt
        # edit that re-pins the SHA256 (lint enforces this) must AUTOMATICALLY
        # invalidate stale entries — even if the author forgot to bump the
        # version label. Patch the hash to two distinct 64-char values across two
        # runs sharing one cache; the judge must be invoked TWICE (cache miss).
        cache: dict[str, Any] = {}
        invocations: list[Any] = []
        judge_fn = self._counting_judge(invocations)
        hash_a = "a" * 64
        hash_b = "b" * 64

        with mock.patch(
            "scripts.claim_audit_pipeline.JUDGE_PROMPT_SHA256", hash_a
        ):
            self.run_pipeline(citations=[_citation()], judge_fn=judge_fn, cache=cache)
        self.assertEqual(len(invocations), 1, "first run must invoke judge")

        with mock.patch(
            "scripts.claim_audit_pipeline.JUDGE_PROMPT_SHA256", hash_b
        ):
            self.run_pipeline(citations=[_citation()], judge_fn=judge_fn, cache=cache)
        self.assertEqual(
            len(invocations), 2,
            "a re-pinned prompt hash MUST invalidate the stale entry and re-invoke "
            "the judge — the default cache-key prompt component is the hash, not the "
            "decoupled version label",
        )


# ---------------------------------------------------------------------------
# T-P4 — Step 2 ref_retrieval_method=failed → LOW-WARN paywall path.
# ---------------------------------------------------------------------------


class TP4FailedRetrievalPaywall(_PipelineTestBase):
    """T-P4: paywall path produces (RETRIEVAL_FAILED, inconclusive, not_applicable, failed)."""

    def test_paywall_triple(self) -> None:
        def paywall(citation: dict[str, Any]) -> dict[str, Any]:
            return {"ref_retrieval_method": "failed", "retrieved_excerpt": None}

        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            raise AssertionError("judge MUST NOT be called on paywall path")

        out = self.run_pipeline(
            citations=[_citation()],
            retrieve_fn=paywall,
            judge_fn=judge_fn,
        )
        self.assertEqual(len(out["claim_audit_results"]), 1)
        e = out["claim_audit_results"][0]
        self.assertEqual(e["judgment"], "RETRIEVAL_FAILED")
        self.assertEqual(e["audit_status"], "inconclusive")
        self.assertEqual(e["defect_stage"], "not_applicable")
        self.assertEqual(e["ref_retrieval_method"], "failed")


# ---------------------------------------------------------------------------
# T-P5 — Step 2 manual_pdf accepted; not_found triggers retrieval_existence.
# ---------------------------------------------------------------------------


class TP5RetrievalPathways(_PipelineTestBase):
    """T-P5: manual_pdf accepted; not_found triggers defect_stage=retrieval_existence."""

    def test_manual_pdf_accepted(self) -> None:
        def manual_pdf(citation: dict[str, Any]) -> dict[str, Any]:
            return {"ref_retrieval_method": "manual_pdf", "retrieved_excerpt": "user-uploaded excerpt"}

        out = self.run_pipeline(citations=[_citation()], retrieve_fn=manual_pdf)
        e = out["claim_audit_results"][0]
        self.assertEqual(e["ref_retrieval_method"], "manual_pdf")
        self.assertEqual(e["judgment"], "SUPPORTED")

    def test_not_found_triggers_retrieval_existence(self) -> None:
        def not_found(citation: dict[str, Any]) -> dict[str, Any]:
            return {"ref_retrieval_method": "not_found", "retrieved_excerpt": None}

        out = self.run_pipeline(citations=[_citation()], retrieve_fn=not_found)
        e = out["claim_audit_results"][0]
        self.assertEqual(e["judgment"], "RETRIEVAL_FAILED")
        self.assertEqual(e["audit_status"], "completed")
        self.assertEqual(e["defect_stage"], "retrieval_existence")
        self.assertEqual(e["ref_retrieval_method"], "not_found")


# ---------------------------------------------------------------------------
# T-P6 — Step 5 judge VIOLATED routes to negative_constraint_violation.
# ---------------------------------------------------------------------------


class TP6ConstraintViolation(_PipelineTestBase):
    """T-P6: cited claim with VIOLATED judge verdict emits claim_audit_result with negative_constraint_violation."""

    def test_violated_routes_to_claim_audit_result(self) -> None:
        manifest = _manifest(
            mncs=[{"constraint_id": "MNC-1", "rule": "No causal language without RCT."}],
        )
        out = self.run_pipeline(
            citations=[_citation()],
            manifests=[manifest],
            judge_fn=_judge_violated(violated_constraint_id="MNC-1"),
        )
        results = out["claim_audit_results"]
        self.assertEqual(len(results), 1)
        e = results[0]
        self.assertEqual(e["judgment"], "UNSUPPORTED")
        self.assertEqual(e["defect_stage"], "negative_constraint_violation")
        self.assertEqual(e["violated_constraint_id"], "MNC-1")
        self.assertEqual(out["constraint_violations"], [], "cited violation MUST emit into claim_audit_results, not constraint_violations")


# ---------------------------------------------------------------------------
# T-P7 — Step 6 defect_stage classification fixtures.
# ---------------------------------------------------------------------------


class TP7DefectStageClassification(_PipelineTestBase):
    """T-P7: each of 6 substantive defect_stages has a fixture mapping."""

    DEFECT_STAGES_TO_TEST = [
        ("retrieval_existence", "not_found"),
        ("metadata", "api"),
        ("source_description", "api"),
        ("citation_anchor", "api"),
        ("synthesis_overclaim", "api"),
        ("negative_constraint_violation", "api"),
    ]

    def test_each_defect_stage_mappable(self) -> None:
        for defect_stage, method in self.DEFECT_STAGES_TO_TEST:
            with self.subTest(defect_stage=defect_stage):
                # Each defect_stage corresponds to a distinct pipeline path; we
                # exercise the dispatch by configuring retrieval + judge to that
                # combination, then assert the emitted entry carries the right
                # defect_stage tag.
                if defect_stage == "retrieval_existence":
                    out = self.run_pipeline(
                        citations=[_citation()],
                        retrieve_fn=lambda c: {"ref_retrieval_method": "not_found", "retrieved_excerpt": None},
                    )
                elif defect_stage == "negative_constraint_violation":
                    manifest = _manifest(
                        mncs=[{"constraint_id": "MNC-1", "rule": "Rule."}],
                    )
                    out = self.run_pipeline(
                        citations=[_citation()],
                        manifests=[manifest],
                        judge_fn=_judge_violated(violated_constraint_id="MNC-1"),
                    )
                else:
                    out = self.run_pipeline(
                        citations=[_citation()],
                        judge_fn=_judge_unsupported(defect_stage=defect_stage),
                    )
                results = out["claim_audit_results"]
                self.assertEqual(len(results), 1, msg=f"expected 1 row for {defect_stage}")
                self.assertEqual(results[0]["defect_stage"], defect_stage)


# ---------------------------------------------------------------------------
# T-P8 — Precedence rule 1: drift + constraint violation → constraint absorbs drift.
# ---------------------------------------------------------------------------


class TP8DriftConstraintPrecedence(_PipelineTestBase):
    """T-P8: a claim that drifts AND violates a constraint emits only the constraint_audit_result row."""

    def test_constraint_absorbs_drift(self) -> None:
        # Manifest mentions one claim; the prose drifts AND violates.
        manifest = _manifest(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Sample preprints accounted for 67% of corpus.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                }
            ],
            mncs=[{"constraint_id": "MNC-1", "rule": "Rule."}],
        )
        # The emitted citation is for a different claim_text (drifted) AND triggers VIOLATED.
        drifted_cite = _citation(
            claim_id="C-002",  # not in manifest
            claim_text="We observed causality between A and B.",
        )
        out = self.run_pipeline(
            citations=[drifted_cite],
            manifests=[manifest],
            judge_fn=_judge_violated(violated_constraint_id="MNC-1"),
        )
        results = out["claim_audit_results"]
        self.assertEqual(len(results), 1, "must emit claim_audit_result")
        self.assertEqual(results[0]["defect_stage"], "negative_constraint_violation")
        drifts = out["claim_drifts"]
        self.assertEqual(
            drifts,
            [],
            "constraint violation MUST absorb drift signal — no companion claim_drifts[] entry per T-P8",
        )


# ---------------------------------------------------------------------------
# T-P9 — Precedence rule 2: citation_anchor distinct from source_description.
# ---------------------------------------------------------------------------


class TP9AnchorVsDescription(_PipelineTestBase):
    """T-P9: anchor-wrong + description-correct => defect_stage=citation_anchor (not source_description)."""

    def test_anchor_wrong_description_correct(self) -> None:
        out = self.run_pipeline(
            citations=[_citation()],
            judge_fn=_judge_unsupported(defect_stage="citation_anchor"),
        )
        e = out["claim_audit_results"][0]
        self.assertEqual(e["defect_stage"], "citation_anchor")
        self.assertNotEqual(e["defect_stage"], "source_description")


# ---------------------------------------------------------------------------
# T-P10 — Precedence rule 3: uncited + manifest-claim sentence => uncited_assertion only.
# ---------------------------------------------------------------------------


class TP10UncitedOverDrift(_PipelineTestBase):
    """T-P10: a sentence that is BOTH uncited AND a drifted manifest claim emits only uncited_assertions[]."""

    def test_uncited_takes_precedence_over_drift(self) -> None:
        manifest = _manifest()
        # The emitted draft contains an uncited sentence (no ref) AND it differs from manifest -> drift.
        uncited_sentences = [
            {
                "sentence_text": "Half of all submissions showed positive results.",
                "section_path": "3. Results",
                "manifest_claim_id": None,
                # Detector-supplied per the v3.8 Step 6 contract: callers
                # must pre-process raw sentences through
                # detect_uncited_assertions (or surface explicit
                # trigger_tokens). _uncited_assertion_entry raises if both
                # the keyword arg and this field are missing.
                "trigger_tokens": ["showed"],
            }
        ]
        out = self.run_pipeline(
            citations=[],  # no citation -> no claim_audit_result row
            manifests=[manifest],
            uncited_sentences=uncited_sentences,
        )
        self.assertEqual(out["claim_audit_results"], [], "uncited sentence has no ref -> no claim_audit_result row")
        self.assertEqual(len(out["uncited_assertions"]), 1, "uncited entry MUST emit")
        # Sentence is not in manifest, and a companion claim_drifts[] entry would
        # also be a natural drift signal — but precedence rule 3 forbids the drift
        # row when uncited fires for the same sentence.
        same_text_drift = [d for d in out["claim_drifts"] if d.get("claim_text") == uncited_sentences[0]["sentence_text"]]
        self.assertEqual(
            same_text_drift,
            [],
            "no companion claim_drifts[] entry for the same sentence per T-P10 / D-INV-4",
        )


# ---------------------------------------------------------------------------
# T-P11 — Cap sampling behavior.
# ---------------------------------------------------------------------------


class TP11CapSampling(_PipelineTestBase):
    """T-P11: N>cap emits stratified summary; N<=cap emits no summary OR telemetry summary; cap=0 rejected."""

    def test_large_n_emits_stratified_summary(self) -> None:
        # 150 citations, cap=100 -> exactly 1 sampling summary, audited_count=100.
        citations = [
            _citation(
                claim_id=f"C-{i:03d}",
                ref_slug=f"ref-{i:03d}",
                scoped_manifest_id=MANIFEST_ID,
            )
            for i in range(1, 151)
        ]
        # Manifest carries 150 claims to satisfy INV-15 cross-array integrity.
        big_manifest = _manifest(
            claims=[
                {
                    "claim_id": f"C-{i:03d}",
                    "claim_text": f"Claim {i}.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                }
                for i in range(1, 151)
            ],
        )
        out = self.run_pipeline(
            citations=citations,
            manifests=[big_manifest],
            config=_config(max_claims_per_paper=100),
        )
        samplings = out["audit_sampling_summaries"]
        self.assertEqual(len(samplings), 1)
        s = samplings[0]
        self.assertEqual(s["audited_count"], 100)
        self.assertEqual(s["total_citation_count"], 150)
        self.assertEqual(s["max_claims_per_paper"], 100)
        self.assertEqual(s["sampling_strategy"], "stratified_buckets_v1")
        indices = s["audited_indices"]
        self.assertEqual(len(indices), 100)
        self.assertEqual(sorted(set(indices)), indices, "audited_indices strictly ascending and unique")

    def test_small_n_no_summary_or_telemetry(self) -> None:
        # 50 citations, cap=100 -> no summary OR summary with audited_count == total.
        citations = [_citation(claim_id=f"C-{i:03d}", ref_slug=f"ref-{i:03d}") for i in range(1, 51)]
        manifest = _manifest(
            claims=[
                {
                    "claim_id": f"C-{i:03d}",
                    "claim_text": f"Claim {i}.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                }
                for i in range(1, 51)
            ],
        )
        out = self.run_pipeline(citations=citations, manifests=[manifest], config=_config(max_claims_per_paper=100))
        samplings = out["audit_sampling_summaries"]
        # Two valid outcomes per spec §4 step 3: zero summaries OR exactly one
        # telemetry-mode summary where audited_count == total_citation_count.
        if samplings:
            self.assertEqual(len(samplings), 1)
            self.assertEqual(samplings[0]["audited_count"], 50)
            self.assertEqual(samplings[0]["total_citation_count"], 50)

    def test_cap_zero_rejected(self) -> None:
        with self.assertRaises((ValueError, AssertionError)):
            self.run_pipeline(
                citations=[_citation()],
                config=_config(max_claims_per_paper=0),
            )


# ---------------------------------------------------------------------------
# T-P12 — Judge invocation failure mapping to INV-14 audit_tool_failure rows.
# Spec §4 step 2 + INV-14; Step 13 R1 codex P1 finding (judge errors must not
# abort the audit pass — they MUST surface as MED-WARN audit_tool_failure rows).
# ---------------------------------------------------------------------------


class TP12JudgeFailureAuditToolFailure(_PipelineTestBase):
    """T-P12: judge_fn exceptions / malformed output → audit_tool_failure row."""

    def _run_one(self, judge_fn: Any) -> dict[str, Any]:
        return self.run_pipeline(citations=[_citation()], judge_fn=judge_fn)

    def _assert_audit_tool_failure(self, out: dict[str, Any], expected_tag: str) -> None:
        results = out["claim_audit_results"]
        self.assertEqual(len(results), 1, "exactly one row emitted on judge failure")
        e = results[0]
        self.assertEqual(e["judgment"], "RETRIEVAL_FAILED")
        self.assertEqual(e["audit_status"], "inconclusive")
        self.assertEqual(e["defect_stage"], "not_applicable")
        self.assertEqual(e["ref_retrieval_method"], "audit_tool_failure")
        self.assertTrue(
            e["rationale"].startswith(expected_tag + ":"),
            f"rationale must lead with INV-14 fault-class tag {expected_tag!r}; got {e['rationale']!r}",
        )

    def test_timeout_error_becomes_judge_timeout(self) -> None:
        def judge_fn(**_kw: Any) -> dict[str, Any]:
            raise TimeoutError("judge call exceeded 30s")

        self._assert_audit_tool_failure(self._run_one(judge_fn), "judge_timeout")

    def test_value_error_becomes_judge_parse_error(self) -> None:
        def judge_fn(**_kw: Any) -> dict[str, Any]:
            raise ValueError("response payload was not parseable")

        self._assert_audit_tool_failure(self._run_one(judge_fn), "judge_parse_error")

    def test_generic_exception_becomes_judge_api_error(self) -> None:
        def judge_fn(**_kw: Any) -> dict[str, Any]:
            raise RuntimeError("upstream returned 503")

        self._assert_audit_tool_failure(self._run_one(judge_fn), "judge_api_error")

    def test_malformed_return_missing_judgment_key(self) -> None:
        def judge_fn(**_kw: Any) -> dict[str, Any]:
            return {"rationale": "shaped wrong"}

        self._assert_audit_tool_failure(self._run_one(judge_fn), "judge_parse_error")

    def test_malformed_return_non_dict(self) -> None:
        def judge_fn(**_kw: Any) -> dict[str, Any]:
            return "this is not a dict"  # type: ignore[return-value]

        self._assert_audit_tool_failure(self._run_one(judge_fn), "judge_parse_error")

    def test_unknown_judgment_value_rejected(self) -> None:
        # Step 13 R2 codex P2: _invoke_judge must validate the judgment enum,
        # not only check key presence. An unknown value MUST map to
        # judge_parse_error rather than reach passport-lint stage.
        def judge_fn(**_kw: Any) -> dict[str, Any]:
            return {"judgment": "MAYBE_SUPPORTED", "rationale": "garbage"}

        self._assert_audit_tool_failure(self._run_one(judge_fn), "judge_parse_error")

    def test_violated_without_constraint_id_rejected(self) -> None:
        # Step 13 R2 codex P2: VIOLATED without a violated_constraint_id would
        # otherwise emit an INV-7-failing negative_constraint_violation row.
        # Reject at invocation boundary instead.
        def judge_fn(**_kw: Any) -> dict[str, Any]:
            return {"judgment": "VIOLATED", "rationale": "missing id"}

        self._assert_audit_tool_failure(self._run_one(judge_fn), "judge_parse_error")

    def test_violated_with_blank_constraint_id_rejected(self) -> None:
        def judge_fn(**_kw: Any) -> dict[str, Any]:
            return {
                "judgment": "VIOLATED",
                "violated_constraint_id": "   ",
                "rationale": "whitespace id",
            }

        self._assert_audit_tool_failure(self._run_one(judge_fn), "judge_parse_error")

    def test_cited_path_rejects_retrieval_failed_verdict(self) -> None:
        # Step 13 R3 codex P2 #2: cited path must not accept RETRIEVAL_FAILED
        # / NOT_VIOLATED — they would crash in _judge_result_entry.
        def judge_fn(**_kw: Any) -> dict[str, Any]:
            return {"judgment": "RETRIEVAL_FAILED", "rationale": "wrong path"}

        self._assert_audit_tool_failure(self._run_one(judge_fn), "judge_parse_error")

    def test_cited_path_rejects_not_violated_verdict(self) -> None:
        def judge_fn(**_kw: Any) -> dict[str, Any]:
            return {"judgment": "NOT_VIOLATED", "rationale": "wrong path"}

        self._assert_audit_tool_failure(self._run_one(judge_fn), "judge_parse_error")

    def test_violated_id_outside_active_set_rejected(self) -> None:
        # Step 13 R3 codex P2 #1: VIOLATED with an id the author never declared
        # would otherwise gate-refuse the formatter on a hallucinated rule.
        # The default _citation() has no active constraints, so any nonblank
        # id is outside the active set.
        def judge_fn(**_kw: Any) -> dict[str, Any]:
            return {
                "judgment": "VIOLATED",
                "violated_constraint_id": "MNC-99",
                "rationale": "hallucinated constraint",
            }

        self._assert_audit_tool_failure(self._run_one(judge_fn), "judge_parse_error")

    # Step 13 R8 codex P2-3 — judgment isinstance(str) guard before set
    # membership. Pre-fix: a malformed return like {"judgment": [1, 2], ...}
    # raised TypeError("unhashable type: 'list'") inside the set membership
    # test, aborting the audit. Post-fix: translation boundary catches it
    # as judge_parse_error → audit_tool_failure (#120 P2-3).

    def test_judgment_non_string_list_becomes_judge_parse_error(self) -> None:
        def judge_fn(**_kw: Any) -> dict[str, Any]:
            return {"judgment": [1, 2], "rationale": "unhashable list"}

        self._assert_audit_tool_failure(self._run_one(judge_fn), "judge_parse_error")

    def test_judgment_non_string_dict_becomes_judge_parse_error(self) -> None:
        def judge_fn(**_kw: Any) -> dict[str, Any]:
            return {"judgment": {"nested": "obj"}, "rationale": "unhashable dict"}

        self._assert_audit_tool_failure(self._run_one(judge_fn), "judge_parse_error")


# ---------------------------------------------------------------------------
# T-P14 — retrieve_fn invocation failure mapping to INV-14 retrieval_* tags.
# Spec §4 step 2 + INV-14; Step 13 R2 codex P2 finding (symmetric to TP12 —
# transient retrieval errors must surface as audit_tool_failure rows).
# ---------------------------------------------------------------------------


class TP14RetrieveFailureAuditToolFailure(_PipelineTestBase):
    """T-P14: retrieve_fn exceptions / malformed output → audit_tool_failure row."""

    def _run_one(self, retrieve_fn: Any) -> dict[str, Any]:
        return self.run_pipeline(citations=[_citation()], retrieve_fn=retrieve_fn)

    def _assert_audit_tool_failure(self, out: dict[str, Any], expected_tag: str) -> None:
        results = out["claim_audit_results"]
        self.assertEqual(len(results), 1)
        e = results[0]
        self.assertEqual(e["judgment"], "RETRIEVAL_FAILED")
        self.assertEqual(e["audit_status"], "inconclusive")
        self.assertEqual(e["defect_stage"], "not_applicable")
        self.assertEqual(e["ref_retrieval_method"], "audit_tool_failure")
        self.assertTrue(
            e["rationale"].startswith(expected_tag + ":"),
            f"rationale must lead with INV-14 fault-class tag {expected_tag!r}; got {e['rationale']!r}",
        )

    def test_timeout_error_becomes_retrieval_timeout(self) -> None:
        def retrieve_fn(_c: dict[str, Any]) -> dict[str, Any]:
            raise TimeoutError("retrieval exceeded 60s")

        self._assert_audit_tool_failure(self._run_one(retrieve_fn), "retrieval_timeout")

    def test_connection_error_becomes_retrieval_network_error(self) -> None:
        def retrieve_fn(_c: dict[str, Any]) -> dict[str, Any]:
            raise ConnectionError("DNS resolution failed")

        self._assert_audit_tool_failure(self._run_one(retrieve_fn), "retrieval_network_error")

    def test_generic_exception_becomes_retrieval_api_error(self) -> None:
        def retrieve_fn(_c: dict[str, Any]) -> dict[str, Any]:
            raise RuntimeError("upstream returned 503")

        self._assert_audit_tool_failure(self._run_one(retrieve_fn), "retrieval_api_error")

    def test_malformed_return_non_dict(self) -> None:
        def retrieve_fn(_c: dict[str, Any]) -> dict[str, Any]:
            return ["not a dict"]  # type: ignore[return-value]

        self._assert_audit_tool_failure(self._run_one(retrieve_fn), "retrieval_api_error")

    def test_malformed_return_missing_ref_retrieval_method(self) -> None:
        def retrieve_fn(_c: dict[str, Any]) -> dict[str, Any]:
            return {"retrieved_excerpt": "no method key"}

        self._assert_audit_tool_failure(self._run_one(retrieve_fn), "retrieval_api_error")

    def test_malformed_return_unknown_method(self) -> None:
        def retrieve_fn(_c: dict[str, Any]) -> dict[str, Any]:
            return {"ref_retrieval_method": "magic_protocol"}

        self._assert_audit_tool_failure(self._run_one(retrieve_fn), "retrieval_api_error")

    def test_malformed_return_non_string_method(self) -> None:
        # Step 13 R8 codex P2-4: ref_retrieval_method as a list raises
        # TypeError on set membership outside the translation boundary;
        # must surface as retrieval_api_error → audit_tool_failure.
        def retrieve_fn(_c: dict[str, Any]) -> dict[str, Any]:
            return {"ref_retrieval_method": ["api", "manual_pdf"], "retrieved_excerpt": "n/a"}

        self._assert_audit_tool_failure(self._run_one(retrieve_fn), "retrieval_api_error")

    def test_api_method_without_excerpt_rejected(self) -> None:
        # Step 13 R3 codex P2 #3 — api with empty excerpt would let the judge
        # mark SUPPORTED with no source text.
        def retrieve_fn(_c: dict[str, Any]) -> dict[str, Any]:
            return {"ref_retrieval_method": "api", "retrieved_excerpt": ""}

        self._assert_audit_tool_failure(self._run_one(retrieve_fn), "retrieval_api_error")

    def test_manual_pdf_with_none_excerpt_rejected(self) -> None:
        def retrieve_fn(_c: dict[str, Any]) -> dict[str, Any]:
            return {"ref_retrieval_method": "manual_pdf", "retrieved_excerpt": None}

        self._assert_audit_tool_failure(self._run_one(retrieve_fn), "retrieval_api_error")


# ---------------------------------------------------------------------------
# T-P13 — EMITTED_NOT_INTENDED set-dedup per D6 (Step 13 R1 codex P2).
# When the same drifted claim_text carries multiple citation markers (e.g.
# one sentence with two ref slugs), one drift row should emit, not one per
# citation.
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# T-P16 — Uncited stream split (Step 13 R4 codex P1 #2).
# Constraint judging runs over the full uncited set; uncited_assertion[]
# LOW-WARN advisory runs over the D4-c filtered subset.
# ---------------------------------------------------------------------------


class TP21UncitedClaimLevelNC(_PipelineTestBase):
    """T-P21: Step 13 R7 codex P1 — uncited stream (d) must include claim-level
    NC-C constraints when the sentence binds a manifest_claim_id.

    Pre-fix: only manifest_negative_constraints (MNC-) was passed to the
    judge; NC-C... for the bound claim was silently dropped.
    """

    def test_nc_c_included_when_sentence_binds_claim_id(self) -> None:
        manifest = _manifest(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Bound claim.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                    "negative_constraints": [
                        {
                            "constraint_id": "NC-C001-1",
                            "rule": "MUST NOT generalize beyond cohort.",
                        }
                    ],
                }
            ],
            mncs=[],
        )
        sentence = {
            "sentence_text": "All practitioners benefit.",
            "section_path": "Discussion",
            "manifest_claim_id": "C-001",
            "scoped_manifest_id": MANIFEST_ID,
        }
        seen_ids: list[set[str]] = []

        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            active = kwargs.get("active_constraints") or []
            seen_ids.append({c["constraint_id"] for c in active})
            return {
                "judgment": "VIOLATED",
                "violated_constraint_id": "NC-C001-1",
                "rationale": "Generalizes beyond cohort.",
            }

        out = self.run_pipeline(
            citations=[],
            manifests=[manifest],
            uncited_sentences=[],
            all_uncited_sentences=[sentence],
            judge_fn=judge_fn,
        )
        self.assertEqual(seen_ids, [{"NC-C001-1"}])
        cv = out["constraint_violations"]
        self.assertEqual(len(cv), 1)
        self.assertEqual(cv[0]["violated_constraint_id"], "NC-C001-1")
        self.assertEqual(cv[0]["scoped_manifest_id"], MANIFEST_ID)


class TP22DuplicateMNCIdAcrossManifests(_PipelineTestBase):
    """T-P22: Step 13 R7 codex P2 — when two manifests use the same MNC id
    string (e.g. both have MNC-1), an uncited violation MUST be attributed
    to the correct manifest. Per-manifest judge calls + scope binding by
    construction (not by first-match-wins lookup).
    """

    def test_violation_attributed_to_correct_manifest(self) -> None:
        manifest_a = _manifest(
            manifest_id="M-2026-05-16T09:00:00Z-a111",
            claims=[],
            mncs=[{"constraint_id": "MNC-1", "rule": "MUST NOT use A-words"}],
        )
        manifest_b = _manifest(
            manifest_id="M-2026-05-16T09:00:00Z-b222",
            claims=[],
            mncs=[{"constraint_id": "MNC-1", "rule": "MUST NOT use B-words"}],
        )
        sentence = {
            "sentence_text": "Uses B-words.",
            "section_path": "Discussion",
        }

        # judge_fn distinguishes by rule text: only violates manifest B's rule.
        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            active = kwargs.get("active_constraints") or []
            for c in active:
                if "B-words" in c.get("rule", ""):
                    return {
                        "judgment": "VIOLATED",
                        "violated_constraint_id": "MNC-1",
                        "rationale": "Uses B-words.",
                    }
            return {"judgment": "NOT_VIOLATED", "rationale": "n/a"}

        out = self.run_pipeline(
            citations=[],
            manifests=[manifest_a, manifest_b],
            uncited_sentences=[],
            all_uncited_sentences=[sentence],
            judge_fn=judge_fn,
        )
        cv = out["constraint_violations"]
        self.assertEqual(len(cv), 1, f"exactly one CV row; got {cv!r}")
        # MUST be attributed to manifest B, NOT manifest A (alphabetic first).
        self.assertEqual(
            cv[0]["scoped_manifest_id"],
            "M-2026-05-16T09:00:00Z-b222",
            f"violation MUST attribute to the manifest whose rule the judge actually violated; got {cv[0]['scoped_manifest_id']!r}",
        )


class TP20UncitedSentenceWithoutScope(_PipelineTestBase):
    """T-P20: Step 13 R6 codex P1 — sentences in the documented all_uncited_sentences
    shape (sentence_text + section_path + optional adjacent_text only, NO
    scoped_manifest_id) MUST still trigger the constraint judge.

    Pre-fix: the loop required sentence.get("scoped_manifest_id") to resolve
    constraints, so orchestrator callers following the contract never saw the
    HIGH-WARN-CONSTRAINT-VIOLATION-UNCITED gate fire. The runtime now applies
    every manifest-level MNC when no caller scope is provided; constraint
    violation rows derive their scoped_manifest_id from the violated_constraint_id
    ↔ source-manifest mapping.
    """

    def test_uncited_sentence_no_scope_triggers_mnc_judge(self) -> None:
        manifest = _manifest(
            claims=[],
            mncs=[
                {
                    "constraint_id": "MNC-1",
                    "rule": "MUST NOT use causal language",
                }
            ],
        )
        sentence = {
            "sentence_text": "The program caused outcome improvement.",
            "section_path": "Discussion",
            # No scoped_manifest_id — documented Stage 4 sentence shape.
        }
        out = self.run_pipeline(
            citations=[],
            manifests=[manifest],
            uncited_sentences=[],  # not D4-c-flagged
            all_uncited_sentences=[sentence],
            judge_fn=lambda **kw: {
                "judgment": "VIOLATED",
                "violated_constraint_id": "MNC-1",
                "rationale": "Causal language.",
            },
        )
        cv = out["constraint_violations"]
        self.assertEqual(
            len(cv),
            1,
            f"R6 P1: uncited sentence without scope must reach MNC judge; got {cv!r}",
        )
        # Schema requires concrete scoped_manifest_id matching the M-pattern.
        self.assertEqual(cv[0]["scoped_manifest_id"], MANIFEST_ID)
        self.assertEqual(cv[0]["violated_constraint_id"], "MNC-1")

    def test_caller_provided_scope_restricts_mnc_set(self) -> None:
        # When the caller pins scoped_manifest_id, only that manifest's MNCs
        # apply (cross-manifest leakage prevented).
        manifest_a = _manifest(
            manifest_id="M-aaaa-A",
            claims=[],
            mncs=[{"constraint_id": "MNC-1", "rule": "MUST NOT use A-words"}],
        )
        manifest_b = _manifest(
            manifest_id="M-bbbb-B",
            claims=[],
            mncs=[{"constraint_id": "MNC-2", "rule": "MUST NOT use B-words"}],
        )
        # Sentence pinned to manifest A — judge should only see MNC-1.
        sentence = {
            "sentence_text": "Uses A-words.",
            "section_path": "Discussion",
            "scoped_manifest_id": "M-aaaa-A",
        }
        seen_constraint_ids: list[set[str]] = []

        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            active = kwargs.get("active_constraints") or []
            seen_constraint_ids.append({c["constraint_id"] for c in active})
            return {"judgment": "NOT_VIOLATED", "rationale": "n/a"}

        self.run_pipeline(
            citations=[],
            manifests=[manifest_a, manifest_b],
            uncited_sentences=[],
            all_uncited_sentences=[sentence],
            judge_fn=judge_fn,
        )
        self.assertEqual(
            seen_constraint_ids,
            [{"MNC-1"}],
            "caller-provided scope must restrict judge to that manifest's MNCs",
        )


class TP19ConstraintAbsorptionFullManifestScope(_PipelineTestBase):
    """T-P19: Step 13 R5 codex P3 — when a citation in manifest M violates a
    negative constraint, ALL of M's drift findings are absorbed, including
    same-manifest citations whose claim_id is NOT in M's declared claim set.

    Pre-fix: pair-level absorption (M, cid_in_manifest) plus the violating
    citation's own pair. A different same-manifest emitted citation with
    claim_id=C-999 (drifted) still produced EMITTED_NOT_INTENDED — that
    contradicted the "absorbed in full" precedence rule.
    """

    def test_drifted_claim_id_in_same_manifest_as_violation_absorbed(self) -> None:
        manifest = _manifest(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Manifest claim about X.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                }
            ],
            mncs=[
                {
                    "constraint_id": "MNC-1",
                    "rule": "MUST NOT use causal language",
                }
            ],
        )
        # Citation 1 violates the MNC on a declared claim_id (C-001).
        violating = _citation(
            claim_id="C-001",
            claim_text="Manifest claim about X.",
            ref_slug="ref-violator",
        )
        # Citation 2 is in the SAME manifest but has a drifted (non-manifest)
        # claim_id. Pre-fix: produced an extra EMITTED_NOT_INTENDED row.
        drifted_sibling = _citation(
            claim_id="C-999",
            claim_text="Sibling claim with drifted id.",
            ref_slug="ref-sibling",
        )

        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            ct = kwargs.get("claim_text", "")
            if "X" in ct:
                return {
                    "judgment": "VIOLATED",
                    "violated_constraint_id": "MNC-1",
                    "rationale": "Causal language violates MNC-1.",
                }
            return {"judgment": "SUPPORTED", "rationale": "Cited page supports."}

        out = self.run_pipeline(
            citations=[violating, drifted_sibling],
            manifests=[manifest],
            judge_fn=judge_fn,
        )
        drifts = [d for d in out["claim_drifts"] if d["drift_kind"] == "EMITTED_NOT_INTENDED"]
        self.assertEqual(
            drifts,
            [],
            f"Same-manifest drifted claim_id MUST be absorbed alongside the constraint violation; got {len(drifts)} drift row(s): {drifts!r}",
        )
        # The constraint violation itself still emits.
        cv = [
            r for r in out["claim_audit_results"]
            if r.get("defect_stage") == "negative_constraint_violation"
        ]
        self.assertEqual(len(cv), 1, "constraint violation row MUST emit")

    def test_drift_in_other_manifest_not_absorbed_by_violation_in_first(self) -> None:
        # Cross-manifest absorption is forbidden — manifest A violation MUST
        # NOT silence drift in manifest B.
        manifest_a = _manifest(
            manifest_id="M-aaaa-A",
            claims=[],
            mncs=[
                {"constraint_id": "MNC-1", "rule": "MUST NOT use causal language"}
            ],
        )
        manifest_b = _manifest(
            manifest_id="M-bbbb-B",
            claims=[
                {
                    "claim_id": "C-100",
                    "claim_text": "Manifest B intended claim.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                }
            ],
        )
        violating_a = _citation(
            claim_id="C-001",
            scoped_manifest_id="M-aaaa-A",
            claim_text="Causal claim in A.",
        )

        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            ct = kwargs.get("claim_text", "")
            if "A" in ct:
                return {
                    "judgment": "VIOLATED",
                    "violated_constraint_id": "MNC-1",
                    "rationale": "Causal.",
                }
            return {"judgment": "SUPPORTED", "rationale": "ok"}

        out = self.run_pipeline(
            citations=[violating_a],
            manifests=[manifest_a, manifest_b],
            judge_fn=judge_fn,
        )
        # Manifest B's C-100 is NOT emitted → INTENDED_NOT_EMITTED MUST still fire.
        intended_drift_b = [
            d for d in out["claim_drifts"]
            if d["drift_kind"] == "INTENDED_NOT_EMITTED" and d.get("scoped_manifest_id") == "M-bbbb-B"
        ]
        self.assertEqual(
            len(intended_drift_b),
            1,
            "manifest B drift MUST NOT be absorbed by violation in manifest A",
        )


class TP18ManifestMissingNoSpuriousDrift(_PipelineTestBase):
    """T-P18: MANIFEST-MISSING run (manifests=[]) produces no claim_drifts[]
    rows. There's no pre-commitment baseline to diff against; emitting
    EMITTED_NOT_INTENDED for every citation would be spurious noise on top
    of the MANIFEST-MISSING advisory the formatter already surfaces.
    Step 13 R5 codex P2 #2.
    """

    def test_no_manifest_no_drift_rows(self) -> None:
        from scripts._claim_audit_constants import SENTINEL_MANIFEST_ID

        citation = {
            "claim_id": "C-001",
            "scoped_manifest_id": SENTINEL_MANIFEST_ID,
            "claim_text": "Some supported claim.",
            "ref_slug": "ref-1",
            "anchor_kind": "page",
            "anchor_value": "10",
            "section_path": "Discussion",
        }
        out = self.run_pipeline(
            citations=[citation],
            manifests=[],
            judge_fn=_judge_supported(),
        )
        self.assertEqual(
            out["claim_drifts"],
            [],
            f"MANIFEST-MISSING run must not emit drift rows; got {out['claim_drifts']!r}",
        )
        # Audit row still emits — the fallback is audit-only, not no-op.
        self.assertEqual(len(out["claim_audit_results"]), 1)

    def test_manifest_present_but_empty_claims_no_drift(self) -> None:
        # A manifest with zero claims is equivalent to no baseline; drift
        # detection should still short-circuit.
        empty_manifest = _manifest(claims=[])
        citation = _citation(claim_text="Drifted claim text.")
        out = self.run_pipeline(
            citations=[citation],
            manifests=[empty_manifest],
            judge_fn=_judge_supported(),
        )
        self.assertEqual(out["claim_drifts"], [])


class TP17ManifestMissingSentinelFallback(_PipelineTestBase):
    """T-P17: MANIFEST-MISSING fallback path must not KeyError when caller
    omits scoped_manifest_id from the citation dict.

    Step 13 R4 codex P2 #3 — row builders previously did
    `citation["scoped_manifest_id"]` directly; the caller's _written_scope_for
    helper would default to SENTINEL_MANIFEST_ID but only AFTER row
    construction, so the index lookup crashed before the sentinel could be
    applied. Row builders now use .get(SENTINEL_MANIFEST_ID) so the fallback
    path works end-to-end.
    """

    def test_citation_without_scoped_manifest_id_emits_sentinel_row(self) -> None:
        citation = {
            "claim_id": "C-001",
            "claim_text": "Manifest-missing test claim.",
            "ref_slug": "ref-1",
            "anchor_kind": "page",
            "anchor_value": "10",
            # scoped_manifest_id deliberately omitted (MANIFEST-MISSING caller).
        }
        out = self.run_pipeline(
            citations=[citation],
            manifests=[],
            judge_fn=_judge_supported(),
        )
        results = out["claim_audit_results"]
        self.assertEqual(len(results), 1, "fallback row must emit, not KeyError")
        # The caller's _written_scope_for would default to SENTINEL_MANIFEST_ID
        # because no manifest binds this claim_id.
        from scripts._claim_audit_constants import SENTINEL_MANIFEST_ID

        self.assertEqual(results[0]["scoped_manifest_id"], SENTINEL_MANIFEST_ID)


class TP16UncitedStreamSplit(_PipelineTestBase):
    """T-P16: constraint stream (d) sees full uncited set; LOW-WARN sees D4-c only."""

    def _build_manifest_with_mnc(self) -> dict[str, Any]:
        return _manifest(
            claims=[],
            mncs=[
                {
                    "constraint_id": "MNC-1",
                    "rule": "MUST NOT use causal language",
                }
            ],
        )

    def test_constraint_violation_outside_d4c_trigger_still_emitted(self) -> None:
        # Sentence violates MNC ("caused improvement") but lacks D4-c trigger
        # tokens (no quantifier, no "%", no "p<"). Pre-R4 the constraint stream
        # would never see it.
        manifest = self._build_manifest_with_mnc()
        full_uncited = [
            {
                "sentence_text": "The program caused improvement.",
                "section_path": "Discussion",
                "scoped_manifest_id": MANIFEST_ID,
            }
        ]
        d4c_uncited: list[dict[str, Any]] = []  # detector filtered this out

        out = self.run_pipeline(
            citations=[],
            manifests=[manifest],
            uncited_sentences=d4c_uncited,
            all_uncited_sentences=full_uncited,
            judge_fn=lambda **kw: {
                "judgment": "VIOLATED",
                "violated_constraint_id": "MNC-1",
                "rationale": "Uses causal language 'caused'.",
            },
        )
        cv = out["constraint_violations"]
        self.assertEqual(len(cv), 1, "constraint judging must run over full uncited set")
        self.assertEqual(cv[0]["violated_constraint_id"], "MNC-1")
        # The LOW-WARN uncited_assertion is NOT emitted because the sentence
        # was outside D4-c trigger filter.
        self.assertEqual(out["uncited_assertions"], [])

    def test_d4c_positive_emits_both_streams(self) -> None:
        # Sentence is BOTH D4-c-positive AND violates MNC → both rows emit
        # (CV-INV-4 explicitly permits the dual presence).
        manifest = self._build_manifest_with_mnc()
        d4c_sentence = {
            "sentence_text": "The program caused 95% improvement.",
            "section_path": "Discussion",
            "scoped_manifest_id": MANIFEST_ID,
            "trigger_tokens": ["95%"],
        }
        out = self.run_pipeline(
            citations=[],
            manifests=[manifest],
            uncited_sentences=[d4c_sentence],
            all_uncited_sentences=[d4c_sentence],
            judge_fn=lambda **kw: {
                "judgment": "VIOLATED",
                "violated_constraint_id": "MNC-1",
                "rationale": "Causal claim.",
            },
        )
        self.assertEqual(len(out["constraint_violations"]), 1)
        self.assertEqual(len(out["uncited_assertions"]), 1)

    def test_backwards_compat_when_all_uncited_omitted(self) -> None:
        # Legacy caller passes only uncited_sentences (the D4-c subset). The
        # pipeline falls back to using that subset for stream (d) too — the
        # constraint check is narrower than the R4 expansion, but the API
        # surface still works.
        manifest = self._build_manifest_with_mnc()
        d4c_sentence = {
            "sentence_text": "The program caused improvement (p<0.01).",
            "section_path": "Discussion",
            "scoped_manifest_id": MANIFEST_ID,
            "trigger_tokens": ["p<0.01"],
        }
        out = self.run_pipeline(
            citations=[],
            manifests=[manifest],
            uncited_sentences=[d4c_sentence],
            # all_uncited_sentences intentionally omitted — defaults to
            # uncited_sentences for backwards compat.
            judge_fn=lambda **kw: {
                "judgment": "VIOLATED",
                "violated_constraint_id": "MNC-1",
                "rationale": "Causal claim.",
            },
        )
        self.assertEqual(len(out["constraint_violations"]), 1)
        self.assertEqual(len(out["uncited_assertions"]), 1)


# ---------------------------------------------------------------------------
# T-P15 — Malformed cache hit → cache_corruption audit_tool_failure row.
# Step 13 R3 codex P2 #4: persistent or injected cache entries can carry
# malformed values; revalidate every hit before routing.
# ---------------------------------------------------------------------------


class TP15CacheCorruption(_PipelineTestBase):
    """T-P15: cache hit re-validated through _validate_judge_dict."""

    def test_missing_judgment_key_in_cache(self) -> None:
        # Pre-seed cache with a malformed entry that lacks `judgment`.
        cache = {}
        # First populate using a valid run so we know the key shape works.
        invoked: list[Any] = []

        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            invoked.append(kwargs)
            return {"judgment": "SUPPORTED", "rationale": "fresh"}

        # Run once to capture the cache_key the pipeline computes.
        self.run_pipeline(citations=[_citation()], judge_fn=judge_fn, cache=cache)
        self.assertEqual(len(cache), 1)
        cache_key = next(iter(cache))

        # Corrupt the cached value to simulate a stale / partial dump.
        cache[cache_key] = {"rationale": "but no judgment key"}

        out = self.run_pipeline(
            citations=[_citation()],
            judge_fn=lambda **_kw: {"judgment": "SUPPORTED", "rationale": "should not be called"},
            cache=cache,
        )
        results = out["claim_audit_results"]
        self.assertEqual(len(results), 1)
        e = results[0]
        self.assertEqual(e["ref_retrieval_method"], "audit_tool_failure")
        self.assertTrue(
            e["rationale"].startswith("cache_corruption:"),
            f"cache hit failure must use INV-14 cache_corruption tag; got {e['rationale']!r}",
        )

    def test_unknown_judgment_in_cache(self) -> None:
        cache = {}

        def judge_fn(**_kw: Any) -> dict[str, Any]:
            return {"judgment": "SUPPORTED", "rationale": "fresh"}

        self.run_pipeline(citations=[_citation()], judge_fn=judge_fn, cache=cache)
        cache_key = next(iter(cache))
        cache[cache_key] = {"judgment": "GIBBERISH", "rationale": "stale"}

        out = self.run_pipeline(
            citations=[_citation()],
            judge_fn=lambda **_kw: {"judgment": "SUPPORTED", "rationale": "n/a"},
            cache=cache,
        )
        results = out["claim_audit_results"]
        self.assertTrue(results[0]["rationale"].startswith("cache_corruption:"))


class TP13EmittedNotIntendedDedupe(_PipelineTestBase):
    """T-P13: D6 set semantics — one drift row per drifted claim_text."""

    def test_intended_not_emitted_text_match_under_renumbered_claim_id(self) -> None:
        # Step 13 R2 codex P2: when the draft carries the manifest claim_text
        # but under a different claim_id (claim_id was renumbered), the
        # INTENDED_NOT_EMITTED side MUST use the same set-of-text semantics
        # as the EMITTED_NOT_INTENDED side. Otherwise a benign renumbering
        # produces false LOW-WARN drift findings.
        manifest = _manifest(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Renumbered manifest claim about Y.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                }
            ]
        )
        # Drafter emits the same claim_text but assigns claim_id C-999 (e.g.
        # the manifest was authored, then claim_ids reshuffled before prose).
        citations = [
            _citation(
                claim_id="C-999",
                claim_text="Renumbered manifest claim about Y.",
                ref_slug="ref-a",
            )
        ]
        out = self.run_pipeline(citations=citations, manifests=[manifest])
        intended_not_emitted = [
            d for d in out["claim_drifts"] if d["drift_kind"] == "INTENDED_NOT_EMITTED"
        ]
        self.assertEqual(
            intended_not_emitted,
            [],
            "claim_text-match must short-circuit INTENDED_NOT_EMITTED per D6 set semantics",
        )

    def test_two_refs_one_drift(self) -> None:
        # Manifest pre-commits to C-001 only; the drafter emits a different
        # claim_text twice, once per citation marker (typical for a sentence
        # like "X is correlated with Y (Ref1, Ref2)" where the drafter chose
        # not to add this claim to the manifest).
        manifest = _manifest(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Manifest-intended claim about X.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                }
            ]
        )
        drifted_text = "This claim was never in the manifest."
        citations = [
            _citation(
                claim_id="C-001",
                claim_text=drifted_text,
                ref_slug="ref-a",
                anchor_value="10",
            ),
            _citation(
                claim_id="C-001",
                claim_text=drifted_text,
                ref_slug="ref-b",
                anchor_value="20",
            ),
        ]
        out = self.run_pipeline(citations=citations, manifests=[manifest])
        drifts = [d for d in out["claim_drifts"] if d["drift_kind"] == "EMITTED_NOT_INTENDED"]
        self.assertEqual(
            len(drifts),
            1,
            f"D6 Emitted is a set of claim_text — one drifted text + two refs MUST yield 1 drift row; got {len(drifts)}",
        )
        self.assertEqual(drifts[0]["claim_text"], drifted_text)


# ---------------------------------------------------------------------------
# T-P23 — v3.8.2 / #118: uncited path judge outage emits UAF row, not synthetic
# NOT_VIOLATED. Validates the fix for the issue where JudgeInvocationError on
# the uncited constraint-judging path was silently substituted as
# {"judgment": "NOT_VIOLATED", ...}, suppressing HIGH-WARN constraint checks.
# ---------------------------------------------------------------------------


class TP23UncitedJudgeOutageEmitsUAF(_PipelineTestBase):
    """T-P23 (v3.8.2 / #118): JudgeInvocationError on uncited path → UAF row."""

    def _manifest_with_mnc(self) -> dict[str, Any]:
        return _manifest(
            mncs=[{"constraint_id": "MNC-1", "rule": "No causal language without RCT."}],
        )

    def test_uncited_judge_timeout_emits_uaf(self) -> None:
        # judge_fn raises a raw TimeoutError; _invoke_judge maps it to
        # JudgeInvocationError("judge_timeout", ...) per the exception
        # translation layer at scripts/claim_audit_pipeline.py:_invoke_judge.
        def failing_judge(**_kw: Any) -> dict[str, Any]:
            raise TimeoutError("judge timed out after 30s")

        uncited_sentences = [
            {
                "sentence_text": "We observed causality between A and B.",
                "section_path": "4. Discussion > 4.3 Limitations",
                "manifest_claim_id": None,
                "trigger_tokens": ["observed"],
            }
        ]
        out = self.run_pipeline(
            citations=[],
            manifests=[self._manifest_with_mnc()],
            uncited_sentences=uncited_sentences,
            judge_fn=failing_judge,
        )
        uaf = out["uncited_audit_failures"]
        self.assertEqual(
            len(uaf),
            1,
            f"judge_timeout on uncited path MUST emit 1 UAF row; got {uaf}",
        )
        e = uaf[0]
        self.assertEqual(e["fault_class"], "judge_timeout")
        self.assertTrue(
            e["rationale"].startswith("judge_timeout:"),
            f"UAF rationale MUST begin with fault_class prefix; got {e['rationale']!r}",
        )
        # No fake NOT_VIOLATED leaked into constraint_violations[].
        self.assertEqual(
            out["constraint_violations"],
            [],
            "judge_timeout MUST NOT emit a constraint_violations[] row — that would be silent suppression of the HIGH-WARN check (pre-v3.8.2 bug)",
        )
        # No synthetic NOT_VIOLATED leaked into any aggregate either.
        for agg_name in ("claim_audit_results", "constraint_violations"):
            for entry in out.get(agg_name, []):
                rationale = entry.get("rationale", "")
                self.assertNotIn(
                    "judge_fn failure on uncited path",
                    rationale,
                    f"pre-v3.8.2 synthetic NOT_VIOLATED rationale MUST NOT appear in {agg_name}",
                )

    def test_uncited_judge_outage_no_audit_abort(self) -> None:
        # Coverage preservation: an outage on one sentence MUST NOT abort the
        # whole audit. With 3 sentences + judge that fails on the second, we
        # expect: rows for sentence 1, UAF for sentence 2, rows for sentence
        # 3 unaffected. ConnectionError → judge_api_error per _invoke_judge's
        # generic Exception translation branch.
        call_count = [0]

        def selectively_failing_judge(**kw: Any) -> dict[str, Any]:
            call_count[0] += 1
            if call_count[0] == 2:
                raise ConnectionError("transient 5xx on call #2")
            return {"judgment": "NOT_VIOLATED", "rationale": "fine"}

        uncited_sentences = [
            {
                "sentence_text": f"Uncited sentence number {i}.",
                "section_path": f"3. Results > 3.{i}",
                "manifest_claim_id": None,
                "trigger_tokens": ["showed"],
            }
            for i in range(1, 4)
        ]
        out = self.run_pipeline(
            citations=[],
            manifests=[self._manifest_with_mnc()],
            uncited_sentences=uncited_sentences,
            judge_fn=selectively_failing_judge,
        )
        # Exactly 1 UAF row from the call #2 outage; the other two sentences
        # judged fine (NOT_VIOLATED → no CV row, no UAF row).
        self.assertEqual(len(out["uncited_audit_failures"]), 1)
        self.assertEqual(out["uncited_audit_failures"][0]["fault_class"], "judge_api_error")
        # Audit pass did NOT abort — 3 judge invocations attempted.
        self.assertEqual(call_count[0], 3)

    def test_uncited_judge_outage_nc_path_carries_manifest_claim_id(self) -> None:
        # When the sentence is bound to a manifest claim (NC-C path), the UAF
        # row MUST carry the manifest_claim_id so the failure can be traced
        # back to which (manifest, claim) constraint set was being judged.
        # ValueError → judge_parse_error per _invoke_judge translation.
        def failing_judge(**_kw: Any) -> dict[str, Any]:
            raise ValueError("malformed judge output: not JSON")

        manifest = _manifest(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Sample preprints accounted for 67% of corpus.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                    "negative_constraints": [
                        {"constraint_id": "NC-C001-1", "rule": "No causal language."}
                    ],
                }
            ],
        )
        uncited_sentences = [
            {
                "sentence_text": "Sample preprints accounted for 67% of corpus.",
                "section_path": "3. Results > 3.1 Overview",
                "manifest_claim_id": "C-001",
                "scoped_manifest_id": MANIFEST_ID,
                "trigger_tokens": ["67%"],
            }
        ]
        out = self.run_pipeline(
            citations=[],
            manifests=[manifest],
            uncited_sentences=uncited_sentences,
            judge_fn=failing_judge,
        )
        uaf = out["uncited_audit_failures"]
        self.assertEqual(len(uaf), 1)
        self.assertEqual(uaf[0]["manifest_claim_id"], "C-001")
        self.assertEqual(uaf[0]["fault_class"], "judge_parse_error")

    def test_uaf_multi_manifest_claim_id_polarity(self) -> None:
        # Codex cross-model review P2-2 (2026-05-17): when sentence carries
        # manifest_claim_id but is judged against MULTIPLE manifests (no
        # scoped_manifest_id pin), the UAF row's manifest_claim_id must
        # ONLY be set when the current (mid) actually owns the claim
        # binding. Without this guard, a UAF row would inherit a claim_id
        # that doesn't exist in this manifest's claims[], failing UAF-INV-3.
        def failing_judge(**_kw: Any) -> dict[str, Any]:
            raise TimeoutError("judge timed out")

        # Two manifests in the passport. Sentence binds to C-001, which
        # exists ONLY in manifest_a; manifest_b contributes MNCs only.
        # When the sentence is judged against both manifests and BOTH
        # judge calls fail, the UAF row for manifest_a should set
        # manifest_claim_id="C-001"; the UAF row for manifest_b MUST set
        # manifest_claim_id=None (no claim binding in that manifest).
        manifest_a = _manifest(
            manifest_id=MANIFEST_ID,
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Causal claim.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                    "negative_constraints": [
                        {"constraint_id": "NC-C001-1", "rule": "No causal."}
                    ],
                }
            ],
        )
        manifest_b = _manifest(
            manifest_id=MANIFEST_ID_OTHER,
            claims=[
                {
                    "claim_id": "C-002",  # different claim id; C-001 is NOT here
                    "claim_text": "Unrelated claim in manifest_b.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                }
            ],
            mncs=[{"constraint_id": "MNC-1", "rule": "Global rule."}],
        )
        uncited_sentences = [
            {
                "sentence_text": "We observed causality between A and B.",
                "section_path": "4. Discussion > 4.3",
                "manifest_claim_id": "C-001",
                # scoped_manifest_id absent → judge against ALL manifests
                "trigger_tokens": ["observed"],
            }
        ]
        out = self.run_pipeline(
            citations=[],
            manifests=[manifest_a, manifest_b],
            uncited_sentences=uncited_sentences,
            judge_fn=failing_judge,
        )
        uaf = out["uncited_audit_failures"]
        self.assertEqual(len(uaf), 2, f"expected 2 UAF rows (one per manifest); got {uaf}")
        by_mid = {row["scoped_manifest_id"]: row for row in uaf}
        self.assertEqual(by_mid[MANIFEST_ID]["manifest_claim_id"], "C-001")
        self.assertIsNone(
            by_mid[MANIFEST_ID_OTHER]["manifest_claim_id"],
            "manifest_b does not own C-001; UAF row MUST set manifest_claim_id=None to avoid UAF-INV-3 fail",
        )

    def test_uaf_mnc_only_claim_stays_null_manifest_claim_id(self) -> None:
        # Codex R2 P2-1 (2026-05-17): when sentence binds to a claim that
        # exists in the manifest but the claim has NO negative_constraints,
        # the judge call is MNC-only and the UAF row's manifest_claim_id
        # MUST stay null. Pre-R2 fix would set manifest_claim_id to the
        # sentence's claim_id any time the claim resolved, conflating
        # MNC-only outages with NC-C outages for downstream consumers.
        def failing_judge(**_kw: Any) -> dict[str, Any]:
            raise TimeoutError("judge timed out")

        manifest = _manifest(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Claim with no negative_constraints.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                    # IMPORTANT: empty negative_constraints — judge call is MNC-only
                    "negative_constraints": [],
                }
            ],
            mncs=[{"constraint_id": "MNC-1", "rule": "Global rule."}],
        )
        uncited_sentences = [
            {
                "sentence_text": "Sentence bound to C-001 but tested vs MNC-1 only.",
                "section_path": "3.1",
                "manifest_claim_id": "C-001",
                "scoped_manifest_id": MANIFEST_ID,
                "trigger_tokens": ["showed"],
            }
        ]
        out = self.run_pipeline(
            citations=[],
            manifests=[manifest],
            uncited_sentences=uncited_sentences,
            judge_fn=failing_judge,
        )
        uaf = out["uncited_audit_failures"]
        self.assertEqual(len(uaf), 1)
        self.assertIsNone(
            uaf[0]["manifest_claim_id"],
            "claim has no NC entries → judge call was MNC-only → manifest_claim_id must be null per spec §3.6",
        )


class TP24PartialDecomposition(_PipelineTestBase):
    """#213: end-to-end PARTIAL handling through the REAL runtime (_judge_result_entry).

    This is the layer all prior #213 tests skipped — schema/lint tests built rows
    by hand, calibration used a stub judge. These tests drive run_audit_pipeline
    so the prompt-verdict PARTIAL actually flows: judge -> _validate_judge_dict ->
    _judge_result_entry -> emitted claim_audit_result row, then cross-checked
    against both the schema and the INV-19 lint.
    """


    def test_partial_normalizes_to_unsupported_source_description(self) -> None:
        out = self.run_pipeline(citations=[_citation()], judge_fn=_judge_partial())
        results = out["claim_audit_results"]
        self.assertEqual(len(results), 1)
        e = results[0]
        self.assertEqual(e["judgment"], "UNSUPPORTED", "PARTIAL must normalize to UNSUPPORTED (B1)")
        self.assertEqual(e["audit_status"], "completed")
        self.assertEqual(e["defect_stage"], "source_description")

    def test_partial_copies_breakdown_onto_row(self) -> None:
        out = self.run_pipeline(citations=[_citation()], judge_fn=_judge_partial())
        e = out["claim_audit_results"][0]
        self.assertIn("sub_claim_breakdown", e, "breakdown is the machine-readable partial signal")
        bd = e["sub_claim_breakdown"]
        self.assertEqual(len(bd), 2)
        self.assertEqual(bd[0]["sub_verdict"], "SUPPORTED")
        self.assertEqual(bd[1]["sub_verdict"], "UNSUPPORTED")

    def test_partial_row_passes_schema_and_inv19(self) -> None:
        # The emitted row must satisfy BOTH the schema and the INV-19 lint —
        # this is the end-to-end binding the prior layer-isolated tests missed.
        out = self.run_pipeline(citations=[_citation()], judge_fn=_judge_partial())
        findings = self._validate_passport(out)
        self.assertEqual(
            findings, [], f"emitted PARTIAL row must be lint-clean (incl. INV-19); got {findings!r}"
        )

    def test_supported_row_has_no_breakdown(self) -> None:
        # Non-PARTIAL rows must NOT carry sub_claim_breakdown (presence is the signal).
        out = self.run_pipeline(citations=[_citation()], judge_fn=_judge_supported())
        self.assertNotIn("sub_claim_breakdown", out["claim_audit_results"][0])

    def test_malformed_partial_routes_to_judge_parse_error_not_bare_unsupported(self) -> None:
        # A malformed PARTIAL (here: all-SUPPORTED, not true-partial) must NOT
        # silently become a bare UNSUPPORTED. It routes to the judge_parse_error
        # inconclusive triple (the only contract-valid path) — ship-gate review finding.
        bad = [
            {"sub_claim_text": "a", "sub_verdict": "SUPPORTED"},
            {"sub_claim_text": "b", "sub_verdict": "SUPPORTED"},
        ]
        out = self.run_pipeline(
            citations=[_citation()], judge_fn=_judge_partial_malformed(breakdown=bad)
        )
        e = out["claim_audit_results"][0]
        self.assertEqual(e["judgment"], "RETRIEVAL_FAILED", "malformed PARTIAL must NOT become bare UNSUPPORTED")
        self.assertEqual(e["audit_status"], "inconclusive")
        self.assertEqual(e["defect_stage"], "not_applicable")
        self.assertEqual(e["ref_retrieval_method"], "audit_tool_failure")
        self.assertTrue(
            e["rationale"].startswith("judge_parse_error"),
            f"rationale must lead with judge_parse_error tag; got {e['rationale']!r}",
        )
        self.assertNotIn("sub_claim_breakdown", e, "no breakdown on a malformed-PARTIAL inconclusive row")

    def test_malformed_partial_item_missing_sub_claim_text_routes_inconclusive(self) -> None:
        # Ship-gate round-2: an item that passes the verdict-MIX gate but lacks a
        # sub_claim_text would, if copied onto a completed row, emit
        # sub_claim_text=None (schema-invalid). It MUST take the judge_parse_error
        # path instead. This is the item-shape half of is_emittable_partial_breakdown.
        bad = [
            {"sub_claim_text": "first", "sub_verdict": "SUPPORTED"},
            {"sub_verdict": "UNSUPPORTED"},  # missing sub_claim_text
        ]
        out = self.run_pipeline(
            citations=[_citation()], judge_fn=_judge_partial_malformed(breakdown=bad)
        )
        e = out["claim_audit_results"][0]
        self.assertEqual(e["judgment"], "RETRIEVAL_FAILED")
        self.assertEqual(e["audit_status"], "inconclusive")
        self.assertTrue(e["rationale"].startswith("judge_parse_error"))
        self.assertEqual(self._validate_passport(out), [], "fallback row must be lint-clean")

    def test_malformed_partial_item_empty_sub_claim_text_routes_inconclusive(self) -> None:
        bad = [
            {"sub_claim_text": "first", "sub_verdict": "SUPPORTED"},
            {"sub_claim_text": "   ", "sub_verdict": "UNSUPPORTED"},  # blank
        ]
        out = self.run_pipeline(
            citations=[_citation()], judge_fn=_judge_partial_malformed(breakdown=bad)
        )
        self.assertEqual(out["claim_audit_results"][0]["judgment"], "RETRIEVAL_FAILED")

    def test_malformed_partial_item_wrong_evidence_pointer_type_routes_inconclusive(self) -> None:
        # Ship-gate round-3: the runtime COPIES evidence_pointer onto the row, so a
        # wrong-typed one (a number) would emit a schema-invalid completed row. It
        # MUST route to judge_parse_error instead (the evidence_pointer-type half of
        # is_emittable_partial_breakdown).
        bad = [
            {"sub_claim_text": "a", "sub_verdict": "SUPPORTED", "evidence_pointer": 123},
            {"sub_claim_text": "b", "sub_verdict": "UNSUPPORTED"},
        ]
        out = self.run_pipeline(
            citations=[_citation()], judge_fn=_judge_partial_malformed(breakdown=bad)
        )
        e = out["claim_audit_results"][0]
        self.assertEqual(e["judgment"], "RETRIEVAL_FAILED")
        self.assertEqual(e["audit_status"], "inconclusive")
        self.assertTrue(e["rationale"].startswith("judge_parse_error"))
        self.assertEqual(self._validate_passport(out), [], "fallback row must be lint-clean")

    def test_partial_with_null_evidence_pointer_emits_valid_row(self) -> None:
        # A genuine PARTIAL with str + null evidence_pointers is emittable + lint-clean.
        good = [
            {"sub_claim_text": "a", "sub_verdict": "SUPPORTED", "evidence_pointer": "p.4"},
            {"sub_claim_text": "b", "sub_verdict": "UNSUPPORTED", "evidence_pointer": None},
        ]
        out = self.run_pipeline(citations=[_citation()], judge_fn=_judge_partial(breakdown=good))
        e = out["claim_audit_results"][0]
        self.assertEqual(e["judgment"], "UNSUPPORTED")
        self.assertEqual(e["sub_claim_breakdown"][1]["evidence_pointer"], None)
        self.assertEqual(self._validate_passport(out), [])

    def test_malformed_partial_single_item_also_routes_inconclusive(self) -> None:
        out = self.run_pipeline(
            citations=[_citation()],
            judge_fn=_judge_partial_malformed(breakdown=[{"sub_claim_text": "a", "sub_verdict": "SUPPORTED"}]),
        )
        e = out["claim_audit_results"][0]
        self.assertEqual(e["judgment"], "RETRIEVAL_FAILED")
        self.assertEqual(e["audit_status"], "inconclusive")

    def test_malformed_partial_row_passes_lint(self) -> None:
        # The fallback inconclusive row must itself be lint-clean.
        out = self.run_pipeline(
            citations=[_citation()],
            judge_fn=_judge_partial_malformed(
                breakdown=[{"sub_claim_text": "a", "sub_verdict": "SUPPORTED"}]
            ),
        )
        self.assertEqual(self._validate_passport(out), [])

    def test_malformed_partial_with_oversized_text_emits_schema_valid_row(self) -> None:
        # #355 P2#3: the malformed-PARTIAL fallback embeds the offending
        # breakdown's repr in the rationale. A >1000-char sub_claim_text is
        # itself a malformed trigger (is_emittable rejects len>1000), so its repr
        # alone overflows the rationale maxLength=2000 and the "clean inconclusive"
        # fallback row becomes schema-INVALID. The row MUST satisfy the schema.
        # 1700-char text overflows the rationale (measured: 2017 chars > 2000).
        # A judge is an LLM with no pre-emission length guarantee, so an
        # over-long claim or an over-decomposed breakdown is a real malformed
        # input — not a synthetic edge.
        bad = [
            {"sub_claim_text": "x" * 1700, "sub_verdict": "SUPPORTED"},
            {"sub_claim_text": "second", "sub_verdict": "UNSUPPORTED"},
        ]
        out = self.run_pipeline(
            citations=[_citation()], judge_fn=_judge_partial_malformed(breakdown=bad)
        )
        e = out["claim_audit_results"][0]
        self.assertEqual(e["judgment"], "RETRIEVAL_FAILED")
        self.assertEqual(e["audit_status"], "inconclusive")
        self.assertTrue(e["rationale"].startswith("judge_parse_error"))
        self.assertLessEqual(
            len(e["rationale"]), 2000,
            f"fallback rationale must fit schema maxLength=2000; got {len(e['rationale'])}",
        )
        errors = sorted(_CAR_VALIDATOR.iter_errors(e), key=str)
        self.assertEqual(
            errors, [], f"malformed-PARTIAL fallback row must satisfy claim_audit_result schema; got {errors}"
        )
        self.assertEqual(self._validate_passport(out), [], "fallback row must also be lint-clean")

    def test_malformed_partial_short_breakdown_fallback_is_schema_valid(self) -> None:
        # Regression guard: the existing short-breakdown malformed paths
        # (single-item, all-SUPPORTED) must STILL emit schema-valid rows after
        # the #355 P2#3 truncation fix — i.e. the bound must not drop the
        # fault-class tag or mangle short messages that never needed truncating.
        for bad in (
            [{"sub_claim_text": "a", "sub_verdict": "SUPPORTED"}],  # single-item
            [
                {"sub_claim_text": "a", "sub_verdict": "SUPPORTED"},
                {"sub_claim_text": "b", "sub_verdict": "SUPPORTED"},
            ],  # all-supported, not true-partial
        ):
            with self.subTest(bad=bad):
                out = self.run_pipeline(
                    citations=[_citation()], judge_fn=_judge_partial_malformed(breakdown=bad)
                )
                e = out["claim_audit_results"][0]
                self.assertTrue(e["rationale"].startswith("judge_parse_error"))
                self.assertEqual(sorted(_CAR_VALIDATOR.iter_errors(e), key=str), [])


class TP360JudgeRationaleBoundOnSuccessPath(_PipelineTestBase):
    """#360: a judge-returned `rationale` is copied onto SUCCESS-path rows with
    no length bound. A judge is an LLM with no pre-emission length guarantee, so
    an over-long rationale yields a schema-INVALID row on the *clean* success
    path — the same defect class as the #359 fallback fix, but on completed /
    constraint_violation rows rather than the inconclusive fallback. Both
    success-path rationale assignments MUST clamp to the schema maxLength=2000.
    """

    # 2500 > 2000 schema maxLength, so an unbounded copy overflows the row.
    _OVERLONG = "Cited page supports the claim. " + ("y" * 2500)

    def test_completed_row_clamps_overlong_judge_rationale(self) -> None:
        # SUPPORTED verdict → _judge_result_entry completed row (pipeline line 558).
        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            return {"judgment": "SUPPORTED", "rationale": self._OVERLONG}

        out = self.run_pipeline(citations=[_citation()], judge_fn=judge_fn)
        e = out["claim_audit_results"][0]
        self.assertEqual(e["judgment"], "SUPPORTED")
        self.assertEqual(e["audit_status"], "completed")
        # Diagnostic head preserved (so the bound truncates the tail, not the head).
        self.assertTrue(
            e["rationale"].startswith("Cited page supports the claim."),
            f"clamp must preserve the diagnostic head; got {e['rationale'][:60]!r}",
        )
        self.assertLessEqual(
            len(e["rationale"]), 2000,
            f"completed-row rationale must fit schema maxLength=2000; got {len(e['rationale'])}",
        )
        errors = sorted(_CAR_VALIDATOR.iter_errors(e), key=str)
        self.assertEqual(
            errors, [], f"completed row with over-long judge rationale must satisfy schema; got {errors}"
        )
        self.assertEqual(self._validate_passport(out), [], "completed row must also be lint-clean")

    def test_completed_row_keeps_short_rationale_verbatim(self) -> None:
        # Regression guard: a short rationale that never needed truncating must
        # pass through unchanged (the bound must not mangle the common case).
        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            return {"judgment": "SUPPORTED", "rationale": "Cited page contains the figure verbatim."}

        out = self.run_pipeline(citations=[_citation()], judge_fn=judge_fn)
        e = out["claim_audit_results"][0]
        self.assertEqual(e["rationale"], "Cited page contains the figure verbatim.")
        self.assertEqual(sorted(_CAR_VALIDATOR.iter_errors(e), key=str), [])

    def test_constraint_violation_row_clamps_overlong_judge_rationale(self) -> None:
        # VIOLATED uncited claim → _constraint_violation_entry (pipeline line 644).
        manifest = _manifest(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Manifest claim about the cohort.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                }
            ],
            mncs=[{"constraint_id": "MNC-1", "rule": "MUST NOT generalize beyond cohort"}],
        )
        sentence = {
            "sentence_text": "All practitioners benefit.",
            "section_path": "Discussion",
        }

        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            return {
                "judgment": "VIOLATED",
                "violated_constraint_id": "MNC-1",
                "rationale": self._OVERLONG,
            }

        out = self.run_pipeline(
            citations=[],
            manifests=[manifest],
            uncited_sentences=[],
            all_uncited_sentences=[sentence],
            judge_fn=judge_fn,
        )
        cv = out["constraint_violations"]
        self.assertEqual(len(cv), 1, f"exactly one CV row; got {cv!r}")
        e = cv[0]
        self.assertTrue(
            e["rationale"].startswith("Cited page supports the claim."),
            f"clamp must preserve the diagnostic head; got {e['rationale'][:60]!r}",
        )
        self.assertLessEqual(
            len(e["rationale"]), 2000,
            f"constraint_violation rationale must fit schema maxLength=2000; got {len(e['rationale'])}",
        )
        errors = sorted(_CV_VALIDATOR.iter_errors(e), key=str)
        self.assertEqual(
            errors, [], f"constraint_violation row with over-long judge rationale must satisfy schema; got {errors}"
        )
        self.assertEqual(self._validate_passport(out, [manifest]), [], "constraint_violation row must also be lint-clean")


class TP360NonStringJudgeRationale(_PipelineTestBase):
    """#360 follow-up: `_validate_judge_dict` accepts a present-but-null
    `rationale` (it only checks key presence, not value type). The success-path
    clamp must NOT call len() on a non-string value — a JSON-null rationale from
    the judge/cache must degrade to the default placeholder, not abort the audit
    run with TypeError.
    """

    def test_completed_row_null_rationale_falls_back_to_placeholder(self) -> None:
        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            return {"judgment": "SUPPORTED", "rationale": None}

        out = self.run_pipeline(citations=[_citation()], judge_fn=judge_fn)
        e = out["claim_audit_results"][0]
        self.assertEqual(e["rationale"], "(no rationale provided)")
        self.assertEqual(sorted(_CAR_VALIDATOR.iter_errors(e), key=str), [])
        self.assertEqual(self._validate_passport(out), [])

    def test_constraint_violation_null_rationale_falls_back_to_default(self) -> None:
        manifest = _manifest(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Manifest claim about the cohort.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                }
            ],
            mncs=[{"constraint_id": "MNC-1", "rule": "MUST NOT generalize beyond cohort"}],
        )
        sentence = {"sentence_text": "All practitioners benefit.", "section_path": "Discussion"}

        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            return {"judgment": "VIOLATED", "violated_constraint_id": "MNC-1", "rationale": None}

        out = self.run_pipeline(
            citations=[],
            manifests=[manifest],
            uncited_sentences=[],
            all_uncited_sentences=[sentence],
            judge_fn=judge_fn,
        )
        cv = out["constraint_violations"]
        self.assertEqual(len(cv), 1, f"exactly one CV row; got {cv!r}")
        e = cv[0]
        # Non-empty (schema minLength=1) and schema-valid — the null degraded
        # to the default, not to None (which would be schema-invalid).
        self.assertTrue(e["rationale"], "null rationale must degrade to a non-empty default")
        self.assertEqual(sorted(_CV_VALIDATOR.iter_errors(e), key=str), [])
        self.assertEqual(self._validate_passport(out, [manifest]), [])


if __name__ == "__main__":
    unittest.main()
