"""Unit tests for check_compliance_report.py (Schema 12 validator)."""
import json
import subprocess
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script

SCRIPT = Path(__file__).resolve().parent / "check_compliance_report.py"
SCHEMA = Path(__file__).resolve().parent.parent / "shared" / "compliance_report.schema.json"


def _valid_sr_report() -> dict:
    """Returns a fresh fully-valid SR compliance report. Callers may mutate freely."""
    return {
        "mode": "systematic_review",
        "stage": "2.5",
        "generated_at": "2026-04-20T10:00:00Z",
        "prisma_trAIce": {
            "items_total": 17,
            "by_tier": {
                "mandatory": {"total": 9, "pass": 9, "fail": []},
                "highly_recommended": {"total": 1, "pass": 1, "fail": []},
                "recommended": {"total": 4, "pass": 4, "fail": []},
                "optional": {"total": 3, "pass": 3, "fail": []},
            },
            "block_decision": "pass",
        },
        "raise": {
            "mode": "full",
            "principles": {
                "human_oversight": "pass",
                "transparency": "pass",
                "reproducibility": "pass",
                "fit_for_purpose": "pass",
            },
            "principle_evidence": {
                "human_oversight": ["Stage 2: bibliography.yaml L12"],
                "transparency": ["manuscript §Methods L40"],
                "reproducibility": ["passport.repro_lock"],
                "fit_for_purpose": ["Stage 1: scoping.md L5"],
            },
            "roles": {
                "evidence_synthesists": ["manuscript §Acknowledgements"],
                "ai_development_teams": ["CHANGELOG"],
                "methodologists": [],
                "publishers": [],
                "users": [],
                "trainers": [],
                "organisations": [],
                "funders": [],
            },
            "block_decision": "pass",
        },
        "overall_decision": "pass",
        "user_action_required": False,
        "evidence": ["manuscript §Methods"],
    }


def _valid_primary_report() -> dict:
    """Returns a fresh fully-valid primary-research compliance report. Callers may mutate freely."""
    return {
        "mode": "primary_research",
        "stage": "4.5",
        "generated_at": "2026-04-20T11:00:00Z",
        "prisma_trAIce": None,
        "raise": {
            "mode": "principles_only",
            "principles": {
                "human_oversight": "pass",
                "transparency": "warn",
                "reproducibility": "pass",
                "fit_for_purpose": "pass",
            },
            "principle_evidence": {
                "human_oversight": ["manuscript §Limitations"],
                "transparency": [],
                "reproducibility": ["manuscript §Methods"],
                "fit_for_purpose": ["manuscript §Introduction"],
            },
            "block_decision": "warn",
        },
        "overall_decision": "warn",
        "user_action_required": True,
        "evidence": [],
    }


def _run(path: Path) -> subprocess.CompletedProcess:
    return run_script(SCRIPT, str(path))


def _write(path: Path, data: dict) -> None:
    path.write_text(json.dumps(data), encoding="utf-8")


def _run_with(report: dict) -> subprocess.CompletedProcess:
    """Write report to a temp file and run the validator against it."""
    with TemporaryDirectory() as tmp:
        p = Path(tmp) / "r.json"
        _write(p, report)
        return _run(p)


class TestComplianceReportValidator(unittest.TestCase):
    def test_valid_sr_report_passes(self) -> None:
        result = _run_with(_valid_sr_report())
        self.assertEqual(result.returncode, 0, msg=result.stderr)

    def test_valid_primary_report_passes(self) -> None:
        result = _run_with(_valid_primary_report())
        self.assertEqual(result.returncode, 0, msg=result.stderr)

    def test_missing_required_field_fails(self) -> None:
        report = _valid_sr_report()
        del report["overall_decision"]
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)
        self.assertIn("overall_decision", result.stdout + result.stderr)

    def test_invalid_mode_enum_fails(self) -> None:
        report = _valid_sr_report()
        report["mode"] = "random_mode"
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_invalid_stage_enum_fails(self) -> None:
        report = _valid_sr_report()
        report["stage"] = "3.5"
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_primary_with_populated_prisma_trAIce_fails(self) -> None:
        # Schema enforces: mode=primary_research implies prisma_trAIce is null.
        # This cross-field rule was added when hardening the schema per code review.
        report = _valid_primary_report()
        report["prisma_trAIce"] = _valid_sr_report()["prisma_trAIce"]
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_sr_with_null_prisma_trAIce_fails(self) -> None:
        # Cross-field rule: systematic_review requires prisma_trAIce object.
        report = _valid_sr_report()
        report["prisma_trAIce"] = None
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_raise_full_without_roles_fails(self) -> None:
        # Cross-field rule: raise.mode=full requires roles.
        report = _valid_sr_report()
        del report["raise"]["roles"]
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_invalid_scope_pattern_fails(self) -> None:
        # user_override.scope must match PRISMA-trAIce IDs or RAISE principles.
        report = _valid_sr_report()
        report["user_override"] = {
            "decision": True,
            "timestamp": "2026-04-20T12:00:00Z",
            "rationale": "Test invalid scope",
            "scope": ["NOT_AN_ITEM"],
        }
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_extra_top_level_property_fails(self) -> None:
        # additionalProperties: false on top-level rejects typos.
        report = _valid_sr_report()
        report["bogus_extra"] = "x"
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_user_override_missing_rationale_fails(self) -> None:
        report = _valid_sr_report()
        report["user_override"] = {
            "decision": True,
            "timestamp": "2026-04-20T12:00:00Z",
            "rationale": "",
            "scope": ["M4"],
        }
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_user_override_empty_scope_fails(self) -> None:
        report = _valid_sr_report()
        report["user_override"] = {
            "decision": True,
            "timestamp": "2026-04-20T12:00:00Z",
            "rationale": "Insufficient time to backfill M4 details before submission deadline.",
            "scope": [],
        }
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_valid_override_with_real_ids_passes(self) -> None:
        # Positive: scope containing real PRISMA-trAIce IDs and RAISE principle names.
        report = _valid_sr_report()
        report["user_override"] = {
            "decision": True,
            "timestamp": "2026-04-20T12:00:00Z",
            "rationale": "Material unavailable to backfill M4 before venue deadline.",
            "scope": ["M4", "transparency"],
        }
        result = _run_with(report)
        self.assertEqual(result.returncode, 0, msg=result.stderr)

    # --- Fix 6: 8 new tests ---

    def test_invalid_generated_at_format_fails(self) -> None:
        """I1: date-time format enforcement."""
        report = _valid_sr_report()
        report["generated_at"] = "NOT_A_DATE"
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_invalid_override_timestamp_format_fails(self) -> None:
        """I1: date-time format applies to user_override.timestamp too."""
        report = _valid_sr_report()
        report["user_override"] = {
            "decision": True,
            "timestamp": "not-a-timestamp",
            "rationale": "test",
            "scope": ["M4"],
        }
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_items_total_not_17_fails(self) -> None:
        """Schema enforces items_total == 17 (const)."""
        report = _valid_sr_report()
        report["prisma_trAIce"]["items_total"] = 18
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_invalid_decision_enum_fails(self) -> None:
        """$defs.decision enum enforcement (block/warn/pass)."""
        report = _valid_sr_report()
        report["overall_decision"] = "maybe"
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_invalid_principle_status_enum_fails(self) -> None:
        """$defs.principle_status enum enforcement (pass/warn/fail)."""
        report = _valid_sr_report()
        report["raise"]["principles"]["human_oversight"] = "undecided"
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)

    def test_ca3_all_17_pass_empty_evidence_warns(self) -> None:
        """CA-3 fires when all 17 items pass AND evidence[] is empty. Exit 0; warning on stderr."""
        report = _valid_sr_report()
        report["evidence"] = []
        # All tiers already all-pass in _valid_sr_report
        result = _run_with(report)
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertIn("CA-3", result.stderr)

    def test_ca3_mandatory_only_pass_does_not_warn(self) -> None:
        """CA-3 must NOT fire when only Mandatory is all-pass but HR/R/O have failures."""
        report = _valid_sr_report()
        report["prisma_trAIce"]["by_tier"]["highly_recommended"]["pass"] = 0
        report["prisma_trAIce"]["by_tier"]["highly_recommended"]["fail"] = ["M7"]
        report["evidence"] = []
        result = _run_with(report)
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertNotIn("CA-3", result.stderr)

    def test_ca4_principle_pass_no_evidence_warns(self) -> None:
        """CA-4 fires when a RAISE principle is 'pass' but principle_evidence for it is empty."""
        report = _valid_sr_report()
        report["raise"]["principle_evidence"]["transparency"] = []
        result = _run_with(report)
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertIn("CA-4", result.stderr)

    # --- Issue #95: protocol_maturity optional field ---

    def test_protocol_maturity_omitted_passes(self) -> None:
        """Zero-touch: existing reports without protocol_maturity continue to validate."""
        # _valid_sr_report() does not include protocol_maturity; this asserts the baseline.
        report = _valid_sr_report()
        self.assertNotIn("protocol_maturity", report["prisma_trAIce"])
        result = _run_with(report)
        self.assertEqual(result.returncode, 0, msg=result.stderr)

    def test_protocol_maturity_valid_shape_passes(self) -> None:
        """Schema accepts protocol_maturity object with all four required fields."""
        report = _valid_sr_report()
        report["prisma_trAIce"]["protocol_maturity"] = {
            "status": "foundational_proposal",
            "upstream_citation": (
                "Holst D, et al. Transparent Reporting of AI in Systematic "
                "Literature Reviews: Development of the PRISMA-trAIce "
                "Checklist. JMIR AI. 2025. doi:10.2196/80247"
            ),
            "snapshot_date": "2025-12-10",
            "caveat_summary": (
                "PRISMA-trAIce is a foundational proposal developed via "
                "systematic adaptation; items have not yet been empirically "
                "validated across diverse research contexts."
            ),
        }
        result = _run_with(report)
        self.assertEqual(result.returncode, 0, msg=result.stderr)

    def test_protocol_maturity_invalid_status_enum_fails(self) -> None:
        """Invalid status enum (e.g. 'beta') must fail validation."""
        report = _valid_sr_report()
        report["prisma_trAIce"]["protocol_maturity"] = {
            "status": "beta",  # not in enum
            "upstream_citation": "Holst D, et al. JMIR AI. 2025. doi:10.2196/80247",
            "snapshot_date": "2025-12-10",
            "caveat_summary": "Test.",
        }
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)
        self.assertIn("status", result.stdout + result.stderr)

    def test_protocol_maturity_missing_required_subfield_fails(self) -> None:
        """All four sub-fields are required when protocol_maturity is present.

        The schema uses oneOf at the prisma_trAIce level, so the error surfaces
        as "not valid under any of the given schemas" rather than naming the
        specific missing subfield. We only assert that validation fails.
        """
        report = _valid_sr_report()
        report["prisma_trAIce"]["protocol_maturity"] = {
            "status": "foundational_proposal",
            "upstream_citation": "Holst D, et al. JMIR AI. 2025. doi:10.2196/80247",
            "snapshot_date": "2025-12-10",
            # caveat_summary intentionally omitted
        }
        result = _run_with(report)
        self.assertEqual(result.returncode, 1)
        self.assertIn("prisma_trAIce", result.stdout + result.stderr)

    def test_missing_maturity_warning_off_by_default(self) -> None:
        """Without ARS_WARN_MISSING_MATURITY=1, no warning when maturity is omitted.

        Explicitly drop the env var from the subprocess environment so the
        test is deterministic regardless of the developer / CI shell state.
        """
        import os as _os
        import sys as _sys
        report = _valid_sr_report()
        report["prisma_trAIce"].pop("protocol_maturity", None)
        env = _os.environ.copy()
        env.pop("ARS_WARN_MISSING_MATURITY", None)
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "r.json"
            _write(p, report)
            result = subprocess.run(
                [_sys.executable, str(SCRIPT), str(p)],
                capture_output=True,
                text=True,
                env=env,
            )
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertNotIn("protocol_maturity", result.stderr)

    def test_missing_maturity_warning_opt_in(self) -> None:
        """With ARS_WARN_MISSING_MATURITY=1, warn when prisma_trAIce lacks protocol_maturity."""
        from tests.test_helpers import run_script as _run_with_env
        report = _valid_sr_report()
        report["prisma_trAIce"].pop("protocol_maturity", None)
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "r.json"
            _write(p, report)
            result = _run_with_env(
                SCRIPT, str(p),
                extra_env={"ARS_WARN_MISSING_MATURITY": "1"},
            )
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertIn("protocol_maturity", result.stderr)


if __name__ == "__main__":
    unittest.main()
