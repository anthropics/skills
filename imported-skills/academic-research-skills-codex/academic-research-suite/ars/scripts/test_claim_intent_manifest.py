"""Manifest tests for v3.8 claim_ref_alignment_audit_agent (T-M1, T-M2, T-M3).

Per spec §7.3 in
docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md.

These tests pin manifest-level contracts that pipeline-level T-P1..T-P11 do
not exercise:

- **T-M1 — Three-set diff**: emitted ∩ intended ∩ supported with drift
  detection in both directions (`EMITTED_NOT_INTENDED` from drafted prose
  introducing claims the writer did not pre-commit to, `INTENDED_NOT_EMITTED`
  from manifest claims dropped during drafting). Verifies the §"Manifest
  cross-reference (D6)" three-set-diff table directly.

- **T-M2 — Missing manifest**: `manifests=[]` plus the `SENTINEL_MANIFEST_ID`
  on each citation must keep every defect_stage path emitting. Per §9
  acceptance bullet `claim_intent_manifest absent → MANIFEST-MISSING
  advisory + fallback flow exercised in test`. This test pins the
  fallback's pipeline-side invariants (all six substantive defect_stages
  still routable; sentinel propagates through to entries); the
  MANIFEST-MISSING annotation surface itself lives in the finalizer (spec
  §13 step 8) and is not covered here.

- **T-M3 — Constraint inheritance**: an `MNC-{m}` global constraint MUST
  apply to a citation whose claim-level entry only declares an `NC-C{n}-{m}`
  constraint. The judge invocation MUST receive both, in `constraint_id`
  sorted order (`_active_constraints_for_claim` invariant per spec §4 step
  3 + M-INV-3).

Spec §7 names the file `tests/test_claim_intent_manifest.py`. Repo
convention places tests under `scripts/test_*.py` (CI uses
`python -m unittest scripts.test_*`); the spec-named stem is preserved.

Run:
    python -m unittest scripts.test_claim_intent_manifest -v
"""
from __future__ import annotations

import unittest
from typing import Any, Callable

try:
    from scripts.claim_audit_pipeline import run_audit_pipeline
    from scripts._claim_audit_constants import SENTINEL_MANIFEST_ID

    _MODULE_IMPORT_ERR: Exception | None = None
except Exception as exc:  # pragma: no cover — RED-phase import pathway
    _MODULE_IMPORT_ERR = exc
    SENTINEL_MANIFEST_ID = "M-0000-00-00T00:00:00Z-0000"

    def run_audit_pipeline(*args: Any, **kwargs: Any) -> Any:
        raise _MODULE_IMPORT_ERR  # type: ignore[misc]


MANIFEST_ID = "M-2026-05-15T10:00:00Z-a1b2"
MANIFEST_ID_B = "M-2026-05-15T10:00:01Z-c3d4"
AUDIT_RUN_ID = "2026-05-15T10:10:00Z-9f8e"
NOW = "2026-05-15T10:11:00Z"


def _claim(
    *,
    claim_id: str,
    claim_text: str,
    ncs: list[dict[str, str]] | None = None,
    planned_refs: list[str] | None = None,
) -> dict[str, Any]:
    out: dict[str, Any] = {
        "claim_id": claim_id,
        "claim_text": claim_text,
        "intended_evidence_kind": "empirical",
        "planned_refs": planned_refs or [],
    }
    if ncs:
        out["negative_constraints"] = ncs
    return out


def _manifest(
    *,
    manifest_id: str = MANIFEST_ID,
    claims: list[dict[str, Any]],
    mncs: list[dict[str, str]] | None = None,
) -> dict[str, Any]:
    return {
        "manifest_version": "1.0",
        "manifest_id": manifest_id,
        "emitted_by": "synthesis_agent",
        "emitted_at": "2026-05-15T09:55:00Z",
        "claims": claims,
        "manifest_negative_constraints": mncs or [],
    }


def _citation(
    *,
    claim_id: str,
    claim_text: str,
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
        "cache_dir": None,
    }
    base.update(overrides)
    return base


def _retrieval_ok(
    *,
    excerpt: str = "The cited page reports the figure verbatim.",
) -> Callable[[dict[str, Any]], dict[str, Any]]:
    def fn(citation: dict[str, Any]) -> dict[str, Any]:
        return {"ref_retrieval_method": "api", "retrieved_excerpt": excerpt}

    return fn


def _retrieval_failed_paywall() -> Callable[[dict[str, Any]], dict[str, Any]]:
    def fn(citation: dict[str, Any]) -> dict[str, Any]:
        return {"ref_retrieval_method": "failed", "retrieved_excerpt": None}

    return fn


def _retrieval_not_found() -> Callable[[dict[str, Any]], dict[str, Any]]:
    def fn(citation: dict[str, Any]) -> dict[str, Any]:
        return {"ref_retrieval_method": "not_found", "retrieved_excerpt": None}

    return fn


def _retrieval_dispatch(
    by_slug: dict[str, dict[str, Any]],
) -> Callable[[dict[str, Any]], dict[str, Any]]:
    """Per-slug retrieval router so a single run can mix paywall / 200 / 404."""

    def fn(citation: dict[str, Any]) -> dict[str, Any]:
        return by_slug[citation["ref_slug"]]

    return fn


def _judge_dispatch(
    by_claim_text: dict[str, dict[str, Any]],
) -> Callable[..., dict[str, Any]]:
    """Per-claim-text judge router for T-M1's mixed SUPPORTED / UNSUPPORTED / AMBIGUOUS."""
    captured_kwargs: list[dict[str, Any]] = []

    def fn(**kwargs: Any) -> dict[str, Any]:
        captured_kwargs.append(kwargs)
        verdict = by_claim_text[kwargs["claim_text"]]
        return verdict

    fn.captured = captured_kwargs  # type: ignore[attr-defined]
    return fn


class _ManifestTestBase(unittest.TestCase):
    """Skip cleanly when scripts.claim_audit_pipeline is not yet importable.

    During the RED phase (Step 4 of the TDD plan in spec §13), the test
    suite imports cleanly even when the module is missing — the contract
    documents the wished-for API.
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
            "manifests": [],
            "citations": [],
            "corpus": [],
            "config": _config(),
            "audit_run_id": AUDIT_RUN_ID,
            "now_iso": NOW,
            "retrieve_fn": _retrieval_ok(),
            "judge_fn": _judge_dispatch({}),
        }
        defaults.update(kwargs)
        return run_audit_pipeline(**defaults)


# ---------------------------------------------------------------------------
# T-M1 — Three-set diff (emitted ∩ intended ∩ supported, drift detection).
# ---------------------------------------------------------------------------


class TM1ThreeSetDiff(_ManifestTestBase):
    """T-M1: manifest set-diff produces both INTENDED_NOT_EMITTED and EMITTED_NOT_INTENDED."""

    def test_three_set_diff_emits_both_drift_kinds(self) -> None:
        # Manifest intends 3 claims (C-001, C-002, C-003); none of the
        # manifest's claims carry a negative constraint, so no constraint
        # absorption confounds drift detection (T-P8 absorbs ENTIRE manifest
        # when ANY citation in that manifest VIOLATEs).
        manifest = _manifest(
            claims=[
                _claim(
                    claim_id="C-001",
                    claim_text="Sample preprints accounted for 67% of corpus.",
                    planned_refs=["smith2024preprints"],
                ),
                _claim(
                    claim_id="C-002",
                    claim_text="Inflection point appeared in mid-2024.",
                    planned_refs=["zhao2026"],
                ),
                _claim(
                    claim_id="C-003",
                    claim_text="The Pew baseline established trust decline.",
                    planned_refs=["pew2023"],
                ),
            ],
        )

        # Prose emits 4 citations:
        #   - C-001 with original manifest claim_text  → intended ∩ emitted ∩ supported
        #   - C-002 with original manifest claim_text  → intended ∩ emitted, judge AMBIGUOUS (NOT in supported)
        #   - Drifted EMITTED text 1: "Median half-life dropped to 11 days." (NOT in manifest)
        #   - Drifted EMITTED text 2: "Citation density doubled after 2024." (NOT in manifest)
        #   - C-003 manifest claim is DROPPED (intended ∉ emitted)
        emitted_citations = [
            _citation(
                claim_id="C-001",
                claim_text="Sample preprints accounted for 67% of corpus.",
                ref_slug="smith2024preprints",
            ),
            _citation(
                claim_id="C-002",
                claim_text="Inflection point appeared in mid-2024.",
                ref_slug="zhao2026",
                anchor_value="14",
            ),
            _citation(
                claim_id="C-100",  # Drifted — not in manifest claims[]
                claim_text="Median half-life dropped to 11 days.",
                ref_slug="brown2025",
                anchor_value="22",
            ),
            _citation(
                claim_id="C-101",  # Drifted — not in manifest claims[]
                claim_text="Citation density doubled after 2024.",
                ref_slug="jones2025",
                anchor_value="3",
            ),
        ]

        judge_fn = _judge_dispatch(
            {
                "Sample preprints accounted for 67% of corpus.": {
                    "judgment": "SUPPORTED",
                    "rationale": "Cited page contains the 67% figure verbatim.",
                },
                "Inflection point appeared in mid-2024.": {
                    "judgment": "AMBIGUOUS",
                    "defect_stage_hint": "source_description",
                    "rationale": "Source mentions mid-2024 but does not pinpoint inflection.",
                },
                "Median half-life dropped to 11 days.": {
                    "judgment": "SUPPORTED",
                    "rationale": "Source reports the 11-day figure.",
                },
                "Citation density doubled after 2024.": {
                    "judgment": "UNSUPPORTED",
                    "defect_stage_hint": "source_description",
                    "rationale": "Source shows a 1.4x increase, not 2x.",
                },
            }
        )

        out = self.run_pipeline(
            manifests=[manifest],
            citations=emitted_citations,
            judge_fn=judge_fn,
        )

        # ---- Emitted ∩ Intended (manifest claim_text appears in emitted) ----
        manifest_texts = {c["claim_text"] for c in manifest["claims"]}
        emitted_texts = {c["claim_text"] for c in emitted_citations}
        emitted_intersect_intended = manifest_texts & emitted_texts
        self.assertEqual(
            emitted_intersect_intended,
            {
                "Sample preprints accounted for 67% of corpus.",
                "Inflection point appeared in mid-2024.",
            },
            "Setup invariant: expected exactly 2 emitted∩intended texts",
        )

        # ---- Supported subset (judge=SUPPORTED post-pipeline) ----
        supported_texts = {
            r["claim_text"]
            for r in out["claim_audit_results"]
            if r["judgment"] == "SUPPORTED"
        }
        # Drifted "Median half-life..." judged SUPPORTED but is NOT in manifest,
        # so the supported∩intended is C-001 only.
        self.assertEqual(
            supported_texts & manifest_texts,
            {"Sample preprints accounted for 67% of corpus."},
            "supported∩intended must equal the 1 SUPPORTED claim that is also in manifest",
        )

        # Judge invocation count — one call per emitted citation. Pins
        # idempotence: the same fixture should not silently re-judge the
        # same (claim_text, ref, anchor) tuple twice in a single run.
        self.assertEqual(
            len(judge_fn.captured),
            4,
            "expected exactly one judge call per emitted citation (4 citations)",
        )

        drifts = out["claim_drifts"]
        drift_kinds = sorted(d["drift_kind"] for d in drifts)
        self.assertIn("EMITTED_NOT_INTENDED", drift_kinds)
        self.assertIn("INTENDED_NOT_EMITTED", drift_kinds)

        # ---- INTENDED_NOT_EMITTED: C-003 dropped ----
        # Cardinalities below are derived from setup (3 manifest claims;
        # 4 emitted citations; 2 of them drift; 1 manifest claim dropped),
        # NOT a policy on how many drifts may emit. The set assertions
        # that follow pin the content invariant; exact counts only guard
        # against over-emission of duplicate rows.
        intended_not_emitted = [
            d for d in drifts if d["drift_kind"] == "INTENDED_NOT_EMITTED"
        ]
        self.assertEqual(len(intended_not_emitted), 1, "expected exactly C-003 dropped")
        self.assertEqual(intended_not_emitted[0]["manifest_claim_id"], "C-003")
        self.assertEqual(intended_not_emitted[0]["scoped_manifest_id"], MANIFEST_ID)
        self.assertEqual(
            intended_not_emitted[0]["claim_text"],
            "The Pew baseline established trust decline.",
        )

        # ---- EMITTED_NOT_INTENDED: 2 drifted texts ----
        emitted_not_intended = [
            d for d in drifts if d["drift_kind"] == "EMITTED_NOT_INTENDED"
        ]
        self.assertEqual(
            len(emitted_not_intended),
            2,
            "expected exactly 2 EMITTED_NOT_INTENDED drift rows",
        )
        self.assertEqual(
            {d["claim_text"] for d in emitted_not_intended},
            {
                "Median half-life dropped to 11 days.",
                "Citation density doubled after 2024.",
            },
        )
        for d in emitted_not_intended:
            self.assertIsNone(d["manifest_claim_id"])
            self.assertIsNone(d["scoped_manifest_id"])
            self.assertIsNotNone(d["section_path"])


# ---------------------------------------------------------------------------
# T-M2 — Missing manifest: MANIFEST-MISSING fallback, all defect_stages emit.
# ---------------------------------------------------------------------------


class TM2MissingManifestFallback(_ManifestTestBase):
    """T-M2: manifests=[] + sentinel scoped_manifest_id keeps every defect_stage routable."""

    def test_sentinel_fallback_emits_all_defect_stages(self) -> None:
        # Six citations, one per substantive routing path the agent must
        # cover in MANIFEST-MISSING fallback per §9 acceptance criterion.
        # The sentinel scoped_manifest_id MUST propagate through to every
        # emitted entry (INV-15 sentinel branch).
        citations = [
            # Path 1: anchor=none → RETRIEVAL_FAILED + not_applicable + not_attempted.
            _citation(
                claim_id="C-001",
                claim_text="No locator claim.",
                ref_slug="ref1",
                anchor_kind="none",
                anchor_value="",
                scoped_manifest_id=SENTINEL_MANIFEST_ID,
            ),
            # Path 2: retrieval=failed (paywall) → RETRIEVAL_FAILED + not_applicable + failed.
            _citation(
                claim_id="C-002",
                claim_text="Paywalled source claim.",
                ref_slug="ref2_paywall",
                scoped_manifest_id=SENTINEL_MANIFEST_ID,
            ),
            # Path 3: retrieval=not_found → RETRIEVAL_FAILED + retrieval_existence.
            _citation(
                claim_id="C-003",
                claim_text="Fabricated reference claim.",
                ref_slug="ref3_404",
                scoped_manifest_id=SENTINEL_MANIFEST_ID,
            ),
            # Path 4: SUPPORTED.
            _citation(
                claim_id="C-004",
                claim_text="Supported claim.",
                ref_slug="ref4_ok",
                scoped_manifest_id=SENTINEL_MANIFEST_ID,
            ),
            # Path 5: AMBIGUOUS with citation_anchor hint.
            _citation(
                claim_id="C-005",
                claim_text="Ambiguous anchor claim.",
                ref_slug="ref5_ok",
                scoped_manifest_id=SENTINEL_MANIFEST_ID,
            ),
            # Path 6: UNSUPPORTED with synthesis_overclaim hint.
            _citation(
                claim_id="C-006",
                claim_text="Overclaim synthesis claim.",
                ref_slug="ref6_ok",
                scoped_manifest_id=SENTINEL_MANIFEST_ID,
            ),
        ]

        # Per-slug retrieval routing.
        retrieval_table = {
            "ref1": {"ref_retrieval_method": "api", "retrieved_excerpt": "ignored"},
            "ref2_paywall": {"ref_retrieval_method": "failed", "retrieved_excerpt": None},
            "ref3_404": {"ref_retrieval_method": "not_found", "retrieved_excerpt": None},
            "ref4_ok": {"ref_retrieval_method": "api", "retrieved_excerpt": "OK"},
            "ref5_ok": {"ref_retrieval_method": "api", "retrieved_excerpt": "OK"},
            "ref6_ok": {"ref_retrieval_method": "api", "retrieved_excerpt": "OK"},
        }

        judge_fn = _judge_dispatch(
            {
                "Supported claim.": {
                    "judgment": "SUPPORTED",
                    "rationale": "Source contains the assertion.",
                },
                "Ambiguous anchor claim.": {
                    "judgment": "AMBIGUOUS",
                    "defect_stage_hint": "citation_anchor",
                    "rationale": "Anchor points adjacent passage but not exact.",
                },
                "Overclaim synthesis claim.": {
                    "judgment": "UNSUPPORTED",
                    "defect_stage_hint": "synthesis_overclaim",
                    "rationale": "Claim aggregates beyond what the source supports.",
                },
            }
        )

        out = self.run_pipeline(
            manifests=[],
            citations=citations,
            retrieve_fn=_retrieval_dispatch(retrieval_table),
            judge_fn=judge_fn,
        )

        results = out["claim_audit_results"]
        self.assertEqual(
            len(results),
            6,
            "every citation must emit a row in MANIFEST-MISSING fallback (per §9 'all defect_stages still emit')",
        )

        # Sentinel propagation: every entry carries the sentinel scoped_manifest_id.
        for r in results:
            self.assertEqual(
                r["scoped_manifest_id"],
                SENTINEL_MANIFEST_ID,
                f"scoped_manifest_id MUST stay sentinel under MANIFEST-MISSING fallback; got {r['scoped_manifest_id']!r}",
            )

        by_claim = {r["claim_id"]: r for r in results}

        # Path 1 — anchor=none.
        self.assertEqual(by_claim["C-001"]["judgment"], "RETRIEVAL_FAILED")
        self.assertEqual(by_claim["C-001"]["defect_stage"], "not_applicable")
        self.assertEqual(by_claim["C-001"]["ref_retrieval_method"], "not_attempted")

        # Path 2 — paywall.
        self.assertEqual(by_claim["C-002"]["judgment"], "RETRIEVAL_FAILED")
        self.assertEqual(by_claim["C-002"]["defect_stage"], "not_applicable")
        self.assertEqual(by_claim["C-002"]["ref_retrieval_method"], "failed")

        # Path 3 — fabricated.
        self.assertEqual(by_claim["C-003"]["judgment"], "RETRIEVAL_FAILED")
        self.assertEqual(by_claim["C-003"]["defect_stage"], "retrieval_existence")
        self.assertEqual(by_claim["C-003"]["ref_retrieval_method"], "not_found")

        # Path 4 — SUPPORTED.
        self.assertEqual(by_claim["C-004"]["judgment"], "SUPPORTED")
        self.assertIsNone(by_claim["C-004"]["defect_stage"])

        # Path 5 — AMBIGUOUS + citation_anchor.
        self.assertEqual(by_claim["C-005"]["judgment"], "AMBIGUOUS")
        self.assertEqual(by_claim["C-005"]["defect_stage"], "citation_anchor")

        # Path 6 — UNSUPPORTED + synthesis_overclaim.
        self.assertEqual(by_claim["C-006"]["judgment"], "UNSUPPORTED")
        self.assertEqual(by_claim["C-006"]["defect_stage"], "synthesis_overclaim")

        # Aggregate guarantees: every emitted entry stays inside the audit
        # path; nothing leaks to constraint_violations or sampling
        # summaries when no manifest constraints exist.
        self.assertEqual(
            out["constraint_violations"],
            [],
            "no manifest → no MNC/NC scope → no constraint_violations rows",
        )
        self.assertEqual(
            out["audit_sampling_summaries"],
            [],
            "N=6 ≤ cap=100 → no sampling summary",
        )


# ---------------------------------------------------------------------------
# T-M3 — Constraint inheritance: MNC applies even when not redeclared at claim level.
# ---------------------------------------------------------------------------


class TM3ConstraintInheritance(_ManifestTestBase):
    """T-M3: judge_fn receives MNC + claim-level NC merged + sorted by constraint_id."""

    def test_mnc_inherited_alongside_claim_level_nc(self) -> None:
        manifest = _manifest(
            mncs=[
                {
                    "constraint_id": "MNC-1",
                    "rule": "No unqualified causal language.",
                },
            ],
            claims=[
                _claim(
                    claim_id="C-001",
                    claim_text="Treatment caused outcome.",
                    planned_refs=["smith2024"],
                    ncs=[
                        {
                            "constraint_id": "NC-C001-1",
                            "rule": "No claims about secondary endpoints.",
                        }
                    ],
                ),
            ],
        )

        captured: list[dict[str, Any]] = []

        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            captured.append(kwargs)
            return {
                "judgment": "SUPPORTED",
                "rationale": "Source supports the assertion.",
            }

        self.run_pipeline(
            manifests=[manifest],
            citations=[
                _citation(
                    claim_id="C-001",
                    claim_text="Treatment caused outcome.",
                    ref_slug="smith2024",
                )
            ],
            judge_fn=judge_fn,
        )

        self.assertEqual(
            len(captured),
            1,
            "judge MUST be invoked exactly once for the single cited claim",
        )
        ac = captured[0]["active_constraints"]

        ids = [c["constraint_id"] for c in ac]
        self.assertEqual(
            ids,
            ["MNC-1", "NC-C001-1"],
            "active_constraints must be sorted by constraint_id (M-INV-3 + §4 step 3)",
        )

        # Scope tags carried through so downstream readers can distinguish
        # global from claim-scoped (the in-runtime tag the cache excludes).
        scopes_by_id = {c["constraint_id"]: c["scope"] for c in ac}
        self.assertEqual(scopes_by_id, {"MNC-1": "MNC", "NC-C001-1": "NC"})

    def test_claim_without_nc_still_inherits_mnc(self) -> None:
        """M-INV-3: claim-level NC can ADD; cannot DROP global MNC.

        A claim that declares NO claim-level constraints must still see the
        manifest's MNCs in its active_constraints set.
        """
        manifest = _manifest(
            mncs=[
                {
                    "constraint_id": "MNC-1",
                    "rule": "No unqualified causal language.",
                },
                {
                    "constraint_id": "MNC-2",
                    "rule": "No proprietary benchmarks.",
                },
            ],
            claims=[
                _claim(
                    claim_id="C-002",
                    claim_text="Effect observed across all subgroups.",
                    planned_refs=["smith2024"],
                    ncs=None,  # No claim-level NCs.
                ),
            ],
        )

        captured: list[dict[str, Any]] = []

        def judge_fn(**kwargs: Any) -> dict[str, Any]:
            captured.append(kwargs)
            return {
                "judgment": "SUPPORTED",
                "rationale": "Source supports the assertion.",
            }

        self.run_pipeline(
            manifests=[manifest],
            citations=[
                _citation(
                    claim_id="C-002",
                    claim_text="Effect observed across all subgroups.",
                    ref_slug="smith2024",
                )
            ],
            judge_fn=judge_fn,
        )

        ac = captured[0]["active_constraints"]
        ids = [c["constraint_id"] for c in ac]
        self.assertEqual(
            ids,
            ["MNC-1", "MNC-2"],
            "MNCs MUST inherit even when claim declares no NCs (M-INV-3)",
        )


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
