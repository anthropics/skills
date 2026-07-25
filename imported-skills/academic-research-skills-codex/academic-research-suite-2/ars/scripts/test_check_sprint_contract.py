"""Unit tests for check_sprint_contract.py (Schema 13.1 validator)."""
from __future__ import annotations

import json
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script

SCRIPT = Path(__file__).resolve().parent / "check_sprint_contract.py"
SCHEMA = Path(__file__).resolve().parent.parent / "shared" / "sprint_contract.schema.json"
TEMPLATE_FULL = (
    Path(__file__).resolve().parent.parent / "shared" / "contracts" / "reviewer" / "full.json"
)
TEMPLATE_METHOD = (
    Path(__file__).resolve().parent.parent / "shared" / "contracts" / "reviewer" / "methodology_focus.json"
)
TEMPLATE_WRITER_FULL = (
    Path(__file__).resolve().parent.parent / "shared" / "contracts" / "writer" / "full.json"
)
TEMPLATE_EVALUATOR_FULL = (
    Path(__file__).resolve().parent.parent / "shared" / "contracts" / "evaluator" / "full.json"
)


def _load_template(path: Path) -> dict:
    """Load a shipped reviewer contract template as dict."""
    return json.loads(path.read_text(encoding="utf-8"))


def _valid_reviewer_full_contract() -> dict:
    """Returns a fresh fully-valid reviewer_full contract. Callers may mutate freely."""
    return {
        "contract_id": "reviewer/reviewer_full/v1",
        "mode": "reviewer_full",
        "stage": "reviewer_full_review",
        "baseline_version": "v3.6.2",
        "panel_size": 5,
        "acceptance_dimensions": [
            {"id": "D1", "name": "methodology_rigor", "description": "x", "priority": "mandatory"},
            {"id": "D2", "name": "domain_accuracy", "description": "x", "priority": "mandatory"},
            {"id": "D3", "name": "argumentative_coherence", "description": "x", "priority": "mandatory"},
            {"id": "D4", "name": "cross_disciplinary_relevance", "description": "x", "priority": "high"},
            {"id": "D5", "name": "writing_and_structure", "description": "x", "priority": "normal"},
        ],
        "measurement_procedure": {
            "reviewer_must_output_before_paper": ["contract_paraphrase", "scoring_plan"],
            "scoring_plan_schema": {
                "required": [
                    "dimension_id",
                    "what_to_look_for",
                    "what_triggers_block",
                    "what_triggers_warn",
                ]
            },
            "paraphrase_minimum_dimensions": "all",
        },
        "failure_conditions": [
            {
                "condition_id": "F1",
                "severity": 90,
                "cross_reviewer_quantifier": "any",
                "expression": "any mandatory dimension scores 'block'",
                "action": "editorial_decision=reject_or_major_revision",
            },
            {
                "condition_id": "F2",
                "severity": 70,
                "cross_reviewer_quantifier": "majority",
                "expression": "two or more mandatory dimensions score 'warn' or worse",
                "action": "editorial_decision=major_revision",
            },
            {
                "condition_id": "F3",
                "severity": 60,
                "cross_reviewer_quantifier": "any",
                "expression": "any high-priority dimension scores 'block'",
                "action": "editorial_decision=major_revision",
            },
            {
                "condition_id": "F0",
                "severity": 10,
                "cross_reviewer_quantifier": "all",
                "expression": "every mandatory dimension scores 'pass'",
                "action": "editorial_decision=accept",
            },
        ],
    }


class TestSchemaValidation(unittest.TestCase):
    def test_valid_reviewer_full_passes(self):
        from scripts.check_sprint_contract import validate

        errors = validate(_valid_reviewer_full_contract())
        self.assertEqual(errors, [])

    def test_missing_top_level_required_fails(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        del c["acceptance_dimensions"]
        errors = validate(c)
        self.assertTrue(any("acceptance_dimensions" in e for e in errors))

    def test_bad_contract_id_pattern_fails(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["contract_id"] = "BAD"
        errors = validate(c)
        self.assertTrue(any("contract_id" in e.lower() or "pattern" in e for e in errors))

    def test_mode_enum_rejects_quick(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["mode"] = "reviewer_quick"
        errors = validate(c)
        self.assertTrue(any("mode" in e for e in errors))

    def test_additional_top_level_property_fails(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["foo"] = "bar"
        errors = validate(c)
        self.assertTrue(any("foo" in e or "additional" in e.lower() for e in errors))

    def test_agent_amendments_extra_key_fails(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["agent_amendments"] = {"extra_field": "x"}
        errors = validate(c)
        self.assertTrue(any("extra_field" in e or "additional" in e.lower() for e in errors))

    def test_override_ladder_when_present_must_be_exactly_3(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["override_ladder"] = [
            {"round": 1, "trigger": "x", "required": ["rationale"]},
            {"round": 2, "trigger": "x", "required": ["rationale"]},
        ]  # only 2 items
        errors = validate(c)
        self.assertTrue(any("override_ladder" in e or "minItems" in e.lower() for e in errors))

    def test_override_ladder_optional_absence_passes(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        if "override_ladder" in c:
            del c["override_ladder"]
        self.assertEqual(validate(c), [])

    def test_override_ladder_positional_order_enforced(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["override_ladder"] = [
            {"round": 1, "trigger": "x", "required": ["rationale"]},
            {"round": 1, "trigger": "x", "required": ["rationale"]},  # should be 2
            {"round": 3, "trigger": "x", "required": ["rationale"]},
        ]
        errors = validate(c)
        self.assertTrue(any("round" in e or "const" in e.lower() for e in errors))

    def test_priority_enum(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["acceptance_dimensions"][0]["priority"] = "critical"
        errors = validate(c)
        self.assertTrue(any("priority" in e for e in errors))

    def test_dimension_no_scoring_scale_field(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["acceptance_dimensions"][0]["scoring_scale"] = "block|warn|pass"
        errors = validate(c)
        self.assertTrue(any("scoring_scale" in e or "additional" in e.lower() for e in errors))

    def test_acceptance_dimension_id_pattern(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["acceptance_dimensions"][0]["id"] = "d1"
        errors = validate(c)
        self.assertTrue(any("id" in e.lower() or "pattern" in e for e in errors))

    def test_failure_condition_id_pattern(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["failure_conditions"][0]["condition_id"] = "Fail1"
        errors = validate(c)
        self.assertTrue(any("condition_id" in e.lower() or "pattern" in e for e in errors))

    def test_failure_conditions_must_contain_F0_accept_grade(self):
        """Codex review P2-1: removing the F0 accept-grade condition must fail
        schema validation. Without F0 the synthesizer protocol can reach a
        "no condition fired" state where there is no editorial_decision to
        emit, aborting the review round at runtime instead of at CI."""
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["failure_conditions"] = [
            fc for fc in c["failure_conditions"] if fc["condition_id"] != "F0"
        ]
        errors = validate(c)
        self.assertTrue(
            any("contain" in e.lower() or "F0" in e or "accept" in e.lower() for e in errors),
            f"expected contains-clause violation, got: {errors}",
        )

    def test_failure_conditions_F0_must_be_accept_action(self):
        """Codex review P2-1: F0 with non-accept action must fail. F0 is the
        accept-grade reservation per shipped templates §6.1 + §6.2; tying its
        action to editorial_decision=accept at schema level prevents future
        templates from misusing the reserved id."""
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        for fc in c["failure_conditions"]:
            if fc["condition_id"] == "F0":
                fc["action"] = "editorial_decision=reject"
        errors = validate(c)
        self.assertTrue(
            any("F0" in e or "accept" in e.lower() or "contains" in e.lower() for e in errors),
            f"expected F0/accept/contains in errors, got: {errors}",
        )

    def test_scoring_plan_required_must_contain_all_four_canonical_fields(self):
        """Codex review P2-2: scoring_plan_schema.required must list the four
        Phase-1 canonical fields. Empty list or partial list lets a contract
        clear CI while making the Phase 1 hard gate vacuous."""
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["measurement_procedure"]["scoring_plan_schema"]["required"] = []
        errors = validate(c)
        self.assertTrue(
            any("required" in e.lower() or "minItems" in e.lower() or "scoring_plan" in e for e in errors),
            f"expected required/minItems/scoring_plan in errors, got: {errors}",
        )

    def test_scoring_plan_required_rejects_typo_field_names(self):
        """Codex review P2-2: typoed entries (e.g. what_trigger_block instead
        of what_triggers_block) must fail schema validation. Otherwise every
        reviewer fails Phase 1 lint at runtime on nonexistent field names."""
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["measurement_procedure"]["scoring_plan_schema"]["required"] = [
            "dimension_id",
            "what_to_look_for",
            "what_trigger_block",  # typo: missing 's'
            "what_triggers_warn",
        ]
        errors = validate(c)
        self.assertTrue(
            any("enum" in e.lower() or "what_trigger_block" in e for e in errors),
            f"expected enum/what_trigger_block in errors, got: {errors}",
        )

    def test_failure_condition_id_pattern_rejects_leading_zero(self):
        """Audit-induced (Task 2 quality review I-1): leading-zero forms F00,
        F01, F02... must be rejected to keep ordinal tie-break (§3.2 severity
        precedence) unambiguous. Schema pattern is ^F(0|[1-9][0-9]?)$."""
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["failure_conditions"][0]["condition_id"] = "F01"
        errors = validate(c)
        self.assertTrue(any("condition_id" in e.lower() or "pattern" in e for e in errors))
        c["failure_conditions"][0]["condition_id"] = "F00"
        errors = validate(c)
        self.assertTrue(any("condition_id" in e.lower() or "pattern" in e for e in errors))

    def test_failure_condition_requires_severity(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        del c["failure_conditions"][0]["severity"]
        errors = validate(c)
        self.assertTrue(any("severity" in e for e in errors))

    def test_reviewer_mode_failure_condition_requires_quantifier(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        del c["failure_conditions"][0]["cross_reviewer_quantifier"]
        errors = validate(c)
        self.assertTrue(any("cross_reviewer_quantifier" in e for e in errors))

    def test_severity_range(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["failure_conditions"][0]["severity"] = -1
        errors = validate(c)
        self.assertTrue(any("severity" in e or "minimum" in e.lower() for e in errors))
        c["failure_conditions"][0]["severity"] = 101
        errors = validate(c)
        self.assertTrue(any("severity" in e or "maximum" in e.lower() for e in errors))

    def test_cross_reviewer_quantifier_enum(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["failure_conditions"][0]["cross_reviewer_quantifier"] = "plurality"
        errors = validate(c)
        self.assertTrue(any("quantifier" in e or "enum" in e.lower() for e in errors))

    def test_panel_size_required(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        del c["panel_size"]
        errors = validate(c)
        self.assertTrue(any("panel_size" in e for e in errors))

    def test_panel_size_minimum_1(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["panel_size"] = 0
        errors = validate(c)
        self.assertTrue(any("panel_size" in e or "minimum" in e.lower() for e in errors))

    def test_paraphrase_minimum_dimensions_accepts_all_and_integer(self):
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        c["measurement_procedure"]["paraphrase_minimum_dimensions"] = "all"
        self.assertEqual(validate(c), [])
        c["measurement_procedure"]["paraphrase_minimum_dimensions"] = 3
        self.assertEqual(validate(c), [])
        c["measurement_procedure"]["paraphrase_minimum_dimensions"] = 0
        self.assertNotEqual(validate(c), [])
        c["measurement_procedure"]["paraphrase_minimum_dimensions"] = "most"
        self.assertNotEqual(validate(c), [])

    def test_conditional_quantifier_not_required_for_non_reviewer_mode(self):
        """spec §7.1 + spec §3.3: when mode does NOT start with 'reviewer_', the
        allOf branch must NOT require cross_reviewer_quantifier on
        failure_conditions[]. Guards the P2 #12 future-proofing intent so
        v3.6.4 writer/evaluator enum additions stay backward-compatible.

        v3.6.2 schema enum only contains reviewer_* values, so we patch the
        loaded schema in-test to add a hypothetical non-reviewer mode and
        re-validate. We DO NOT modify the on-disk schema."""
        import copy
        from scripts.check_sprint_contract import load_schema
        import jsonschema
        schema = copy.deepcopy(load_schema())
        # Add a non-reviewer-prefixed mode to the enum.
        schema["properties"]["mode"]["enum"].append("writer_full")
        c = _valid_reviewer_full_contract()
        c["mode"] = "writer_full"
        c["contract_id"] = "writer/writer_full/v1"
        c["stage"] = "writer_full_draft"
        # Strip cross_reviewer_quantifier from every failure_condition.
        for fc in c["failure_conditions"]:
            fc.pop("cross_reviewer_quantifier", None)
        validator = jsonschema.Draft202012Validator(
            schema,
            format_checker=jsonschema.Draft202012Validator.FORMAT_CHECKER,
        )
        errors = [str(e.message) for e in validator.iter_errors(c)]
        # No error should mention cross_reviewer_quantifier — the conditional
        # branch in §3.3 only fires when mode starts with 'reviewer_'.
        self.assertFalse(
            any("cross_reviewer_quantifier" in e for e in errors),
            f"Unexpected quantifier error on non-reviewer mode: {errors}",
        )

    def test_shipped_template_full_passes_schema_and_invariants(self):
        from scripts.check_sprint_contract import validate, check_structural_invariants
        contract = _load_template(TEMPLATE_FULL)
        self.assertEqual(validate(contract), [])
        self.assertEqual(check_structural_invariants(contract), [])

    def test_shipped_template_full_produces_zero_soft_warnings(self):
        from scripts.check_sprint_contract import warn_suspicious
        contract = _load_template(TEMPLATE_FULL)
        self.assertEqual(warn_suspicious(contract, "v3.6.2"), [])

    def test_shipped_template_methodology_focus_passes_schema_and_invariants(self):
        from scripts.check_sprint_contract import validate, check_structural_invariants
        contract = _load_template(TEMPLATE_METHOD)
        self.assertEqual(validate(contract), [])
        self.assertEqual(check_structural_invariants(contract), [])

    def test_shipped_template_methodology_focus_produces_zero_soft_warnings(self):
        from scripts.check_sprint_contract import warn_suspicious
        contract = _load_template(TEMPLATE_METHOD)
        self.assertEqual(warn_suspicious(contract, "v3.6.2"), [])


class TestStructuralInvariants(unittest.TestCase):
    def test_structural_invariant_duplicate_dimension_id(self):
        from scripts.check_sprint_contract import check_structural_invariants
        c = _valid_reviewer_full_contract()
        # force duplicate id
        c["acceptance_dimensions"][1] = dict(c["acceptance_dimensions"][1], id="D1")
        errors = check_structural_invariants(c)
        self.assertTrue(any("duplicate" in e.lower() and "id" in e.lower() for e in errors))

    def test_structural_invariant_duplicate_dimension_name(self):
        from scripts.check_sprint_contract import check_structural_invariants
        c = _valid_reviewer_full_contract()
        c["acceptance_dimensions"][1] = dict(c["acceptance_dimensions"][1], name="methodology_rigor")
        errors = check_structural_invariants(c)
        self.assertTrue(any("duplicate" in e.lower() and "name" in e.lower() for e in errors))

    def test_structural_invariant_duplicate_condition_id(self):
        from scripts.check_sprint_contract import check_structural_invariants
        c = _valid_reviewer_full_contract()
        c["failure_conditions"][1] = dict(c["failure_conditions"][1], condition_id="F1")
        errors = check_structural_invariants(c)
        self.assertTrue(any("duplicate" in e.lower() and "condition_id" in e.lower() for e in errors))

    def test_structural_invariant_clean_contract_passes(self):
        from scripts.check_sprint_contract import check_structural_invariants
        self.assertEqual(check_structural_invariants(_valid_reviewer_full_contract()), [])


class TestSoftWarnings(unittest.TestCase):
    def test_sc1_baseline_lag_warns(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_reviewer_full_contract()
        c["baseline_version"] = "v3.3.0"
        warnings = warn_suspicious(c, "v3.6.2")
        self.assertTrue(any("SC-1" in w or "baseline" in w.lower() for w in warnings))

    def test_sc1_no_ars_version_skips(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_reviewer_full_contract()
        c["baseline_version"] = "v3.3.0"
        warnings = warn_suspicious(c, None)
        self.assertFalse(any("SC-1" in w or "baseline" in w.lower() for w in warnings))

    def test_sc1_lag_exactly_2_does_not_warn(self):
        """Boundary: spec §4.3 line 340 says SC-1 fires when baseline 'lags
        current ARS by more than 2 minor versions'. lag == 2 must NOT warn."""
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_reviewer_full_contract()
        c["baseline_version"] = "v3.4.0"  # lag = 2 vs v3.6.2
        warnings = warn_suspicious(c, "v3.6.2")
        self.assertFalse(any("SC-1" in w for w in warnings))

    def test_sc2_single_dimension_warns(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_reviewer_full_contract()
        c["acceptance_dimensions"] = c["acceptance_dimensions"][:1]
        # Remove failure_conditions referencing D2-D5 so we don't trigger SC-4
        c["failure_conditions"] = [
            {
                "condition_id": "F0",
                "severity": 10,
                "cross_reviewer_quantifier": "all",
                "expression": "D1 scores 'pass'",
                "action": "editorial_decision=accept",
            }
        ]
        warnings = warn_suspicious(c, None)
        self.assertTrue(any("SC-2" in w for w in warnings))

    def test_sc3_no_mandatory_warns(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_reviewer_full_contract()
        for d in c["acceptance_dimensions"]:
            d["priority"] = "normal"
        warnings = warn_suspicious(c, None)
        self.assertTrue(any("SC-3" in w for w in warnings))

    def test_sc2_multi_dimension_does_not_warn(self):
        """Negative case: 5-dim default fixture must not trigger SC-2."""
        from scripts.check_sprint_contract import warn_suspicious
        warnings = warn_suspicious(_valid_reviewer_full_contract(), None)
        self.assertFalse(any("SC-2" in w for w in warnings))

    def test_sc3_with_mandatory_does_not_warn(self):
        """Negative case: default fixture has 3 mandatory dims, SC-3 must skip."""
        from scripts.check_sprint_contract import warn_suspicious
        warnings = warn_suspicious(_valid_reviewer_full_contract(), None)
        self.assertFalse(any("SC-3" in w for w in warnings))

    def test_sc4_orphan_dimension_reference_warns(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_reviewer_full_contract()
        c["failure_conditions"].append({
            "condition_id": "F9",
            "severity": 50,
            "cross_reviewer_quantifier": "any",
            "expression": "D9 scores 'block'",  # D9 not in acceptance_dimensions
            "action": "editorial_decision=major_revision",
        })
        warnings = warn_suspicious(c, None)
        self.assertTrue(any("SC-4" in w and "D9" in w for w in warnings))

    def test_sc5_measurement_procedure_missing_required_outputs_warns(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_reviewer_full_contract()
        c["measurement_procedure"]["reviewer_must_output_before_paper"] = ["contract_paraphrase"]
        warnings = warn_suspicious(c, None)
        self.assertTrue(any("SC-5" in w for w in warnings))

    def test_sc6_placeholder_unreachable_on_schema_valid_contract(self):
        """SC-6 was retained in spec as dead-path defense-in-depth — can never
        fire on a schema-valid contract because additionalProperties=false on
        agent_amendments blocks the only condition it checks. Assert that
        warn_suspicious does not emit SC-6 on any schema-valid input."""
        from scripts.check_sprint_contract import warn_suspicious, validate
        c = _valid_reviewer_full_contract()
        self.assertEqual(validate(c), [])  # schema-valid precondition
        warnings = warn_suspicious(c, None)
        self.assertFalse(any("SC-6" in w for w in warnings))

    def test_sc7_conflicting_failure_condition_actions_warns(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_reviewer_full_contract()
        c["failure_conditions"][0]["severity"] = 80
        c["failure_conditions"][0]["action"] = "editorial_decision=reject"
        c["failure_conditions"][2]["severity"] = 80
        c["failure_conditions"][2]["action"] = "editorial_decision=major_revision"
        warnings = warn_suspicious(c, None)
        self.assertTrue(any("SC-7" in w for w in warnings))

    def test_sc9_impossible_paraphrase_minimum_warns(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_reviewer_full_contract()
        c["acceptance_dimensions"] = c["acceptance_dimensions"][:3]  # 3 dims
        # Keep failure_conditions referencing D1..D3 only; drop D4/D5 refs
        c["failure_conditions"] = [
            fc for fc in c["failure_conditions"]
            if "D4" not in fc["expression"] and "D5" not in fc["expression"]
        ]
        c["measurement_procedure"]["paraphrase_minimum_dimensions"] = 5
        warnings = warn_suspicious(c, None)
        self.assertTrue(any("SC-9" in w for w in warnings))

    def test_sc10_unreferenced_mandatory_dimension_warns(self):
        """Add a high-priority D6 AND drop the only high-priority expression
        from the fixture so neither direct id reference nor priority-scope
        expression covers D6. SC-10 should fire."""
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_reviewer_full_contract()
        # Drop F3 ("any high-priority dimension scores 'block'") from fixture
        # so the high-priority class has zero priority-scoped coverage.
        c["failure_conditions"] = [
            fc for fc in c["failure_conditions"] if fc["condition_id"] != "F3"
        ]
        # Drop existing high-priority dim D4 from fixture so it does not
        # contaminate the assertion. Then add a fresh D6 high-priority that
        # has neither id ref nor priority-scope cover.
        c["acceptance_dimensions"] = [
            d for d in c["acceptance_dimensions"] if d["priority"] != "high"
        ]
        c["acceptance_dimensions"].append(
            {"id": "D6", "name": "orphan_criterion", "description": "x", "priority": "high"}
        )
        warnings = warn_suspicious(c, None)
        self.assertTrue(
            any("SC-10" in w and "D6" in w for w in warnings),
            f"expected SC-10 to fire on orphan high-priority D6, got: {warnings}",
        )


    def test_sc11_panel_size_1_warns(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_reviewer_full_contract()
        c["panel_size"] = 1
        warnings = warn_suspicious(c, None)
        self.assertTrue(any("SC-11" in w and "panel_size=1" in w for w in warnings))

    def test_sc11_mode_panel_mismatch_full(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_reviewer_full_contract()
        c["panel_size"] = 3
        warnings = warn_suspicious(c, None)
        self.assertTrue(any("SC-11" in w and "reviewer_full" in w for w in warnings))

    def test_sc11_mode_panel_mismatch_methodology(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_reviewer_full_contract()
        c["mode"] = "reviewer_methodology_focus"
        c["contract_id"] = "reviewer/reviewer_methodology_focus/v1"
        c["panel_size"] = 5
        warnings = warn_suspicious(c, None)
        self.assertTrue(any("SC-11" in w and "reviewer_methodology_focus" in w for w in warnings))


class TestCLI(unittest.TestCase):
    def test_cli_missing_file_returns_1(self):
        result = run_script(SCRIPT, "/nonexistent/path.json")
        self.assertEqual(result.returncode, 1)

    def test_cli_bad_json_returns_1(self):
        with TemporaryDirectory() as tmp:
            bad = Path(tmp) / "bad.json"
            bad.write_text("{not json", encoding="utf-8")
            result = run_script(SCRIPT, str(bad))
            self.assertEqual(result.returncode, 1)

    def test_cli_valid_returns_0(self):
        with TemporaryDirectory() as tmp:
            good = Path(tmp) / "good.json"
            good.write_text(json.dumps(_valid_reviewer_full_contract()), encoding="utf-8")
            result = run_script(SCRIPT, str(good))
            self.assertEqual(result.returncode, 0, result.stderr)


class TestTemplateSemantics(unittest.TestCase):
    def test_full_template_precedence_rule(self):
        """When F1 (severity 90) and F3 (severity 60) both fire in the same round,
        spec §3.2 / §5.5 precedence selects F1. Exercises the rule against the
        shipped template rather than a synthetic contract.

        Severities differ by construction so ordinal tie-break is not exercised
        here (a separate test would be needed for that)."""
        contract = _load_template(TEMPLATE_FULL)
        fired = [
            (fc["severity"], fc["condition_id"], fc["action"])
            for fc in contract["failure_conditions"]
            if fc["condition_id"] in ("F1", "F3")
        ]
        winning = max(fired, key=lambda x: x[0])
        self.assertEqual(winning[1], "F1")
        self.assertEqual(winning[2], "editorial_decision=reject_or_major_revision")


def _valid_writer_full_contract() -> dict:
    """Returns a fresh valid writer_full contract, loaded from the shipped template
    so structural drift between the test and the live template surfaces as a test
    failure rather than test-only divergence."""
    return _load_template(TEMPLATE_WRITER_FULL)


def _valid_evaluator_full_contract() -> dict:
    """Returns a fresh valid evaluator_full contract, loaded from the shipped
    template (same rationale as _valid_writer_full_contract)."""
    return _load_template(TEMPLATE_EVALUATOR_FULL)


class TestSchema131WriterEvaluatorPositive(unittest.TestCase):
    """§7.3 schema-level positive fixtures: shipped writer/evaluator templates
    must validate cleanly under Schema 13.1 + produce zero soft warnings."""

    def test_shipped_writer_full_passes_schema_and_invariants(self):
        from scripts.check_sprint_contract import validate, check_structural_invariants
        c = _valid_writer_full_contract()
        self.assertEqual(validate(c), [])
        self.assertEqual(check_structural_invariants(c), [])

    def test_shipped_writer_full_produces_zero_soft_warnings(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_writer_full_contract()
        self.assertEqual(warn_suspicious(c, "v3.6.6"), [])

    def test_shipped_evaluator_full_passes_schema_and_invariants(self):
        from scripts.check_sprint_contract import validate, check_structural_invariants
        c = _valid_evaluator_full_contract()
        self.assertEqual(validate(c), [])
        self.assertEqual(check_structural_invariants(c), [])

    def test_shipped_evaluator_full_produces_zero_soft_warnings(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_evaluator_full_contract()
        self.assertEqual(warn_suspicious(c, "v3.6.6"), [])


class TestSchema131NegativeBranches(unittest.TestCase):
    """§7.3 schema-level negative fixtures exercising the five v3.6.6 schema
    branches the validator hard-fails (branches 4 / 5 / 6 / 11 / 12 per §3.5).
    Cross-mode field leakage (R1) is intentionally NOT tested as a hard-fail
    here per §7.1 settled decision; v3.7.x not-clause hardening covers that.
    """

    def test_branch_11_writer_full_missing_pre_commitment_artifacts_fails(self):
        from scripts.check_sprint_contract import validate
        c = _valid_writer_full_contract()
        del c["pre_commitment_artifacts"]
        errors = validate(c)
        self.assertTrue(any("pre_commitment_artifacts" in e for e in errors))

    def test_branch_12_evaluator_full_missing_disagreement_handling_fails(self):
        from scripts.check_sprint_contract import validate
        c = _valid_evaluator_full_contract()
        del c["disagreement_handling"]
        errors = validate(c)
        self.assertTrue(any("disagreement_handling" in e for e in errors))

    def test_branch_5_writer_full_action_pinned_to_writer_decision_enum(self):
        """writer_full pinning failure_conditions[].action to an editorial_decision=*
        value (the reviewer enum) must fail under allOf branch 5 + branch 8 (F0)."""
        from scripts.check_sprint_contract import validate
        c = _valid_writer_full_contract()
        for fc in c["failure_conditions"]:
            if fc["condition_id"] == "F1":
                fc["action"] = "editorial_decision=reject_or_major_revision"
                break
        errors = validate(c)
        self.assertTrue(any("action" in e or "enum" in e.lower() for e in errors))

    def test_branch_6_evaluator_full_action_pinned_to_evaluator_decision_enum(self):
        """evaluator_full pinning failure_conditions[].action to a writer_decision=*
        value must fail under allOf branch 6 + branch 9 (F0)."""
        from scripts.check_sprint_contract import validate
        c = _valid_evaluator_full_contract()
        for fc in c["failure_conditions"]:
            if fc["condition_id"] == "F1":
                fc["action"] = "writer_decision=revise_in_phase_4b"
                break
        errors = validate(c)
        self.assertTrue(any("action" in e or "enum" in e.lower() for e in errors))

    def test_branch_4_reviewer_action_mis_pinned_to_generator_enum_fails(self):
        """reviewer_full pinning failure_conditions[].action to a writer_decision=* /
        evaluator_decision=* value must fail under allOf branch 4. Completes the
        cross-mode action-enum triplet coverage."""
        from scripts.check_sprint_contract import validate
        c = _valid_reviewer_full_contract()
        for fc in c["failure_conditions"]:
            if fc["condition_id"] == "F1":
                fc["action"] = "writer_decision=revise_in_phase_4b"
                break
        errors = validate(c)
        self.assertTrue(any("action" in e or "enum" in e.lower() for e in errors))


class TestSchema131ReviewerZeroTouch(unittest.TestCase):
    """§3.6 backward-compat proof: existing reviewer contracts validate identically
    under Schema 13.1. These two test names are explicitly committed by §3.6."""

    def test_existing_reviewer_contracts_still_valid_under_13_1(self):
        """Loads both shipped reviewer templates against Schema 13.1 and asserts
        validation success without modification. §3.6 zero-touch verification."""
        from scripts.check_sprint_contract import validate, check_structural_invariants
        for path in (TEMPLATE_FULL, TEMPLATE_METHOD):
            with self.subTest(template=path.name):
                c = _load_template(path)
                self.assertEqual(validate(c), [])
                self.assertEqual(check_structural_invariants(c), [])

    def test_byte_equivalent_validation_for_reviewer_contracts(self):
        """Asserts that running validate() on each shipped reviewer template under
        Schema 13.1 produces an empty error list — the structural equivalent of
        diffing against the (now-superseded) Schema 13 result, which was also
        empty for these templates. §3.6 promised this regression test."""
        from scripts.check_sprint_contract import validate, warn_suspicious
        for path in (TEMPLATE_FULL, TEMPLATE_METHOD):
            with self.subTest(template=path.name):
                c = _load_template(path)
                self.assertEqual(validate(c), [])
                self.assertEqual(warn_suspicious(c, "v3.6.6"), [])


class TestSC5SC9SC11ModeGating(unittest.TestCase):
    """§7.1 implementation requirement: SC-5 (measurement_procedure missing
    canonical outputs), SC-9 (paraphrase_minimum_dimensions exceeds dim count),
    and SC-11 (panel_size sanity) are reviewer-mode-specific. They must NOT
    fire on clean writer/evaluator templates that intentionally omit the
    reviewer-only fields per §3.3.1 / §3.3.5. Mode-agnostic warnings (SC-1 /
    SC-2 / SC-3 / SC-4 / SC-7 / SC-10) continue to fire across all modes."""

    def test_sc5_does_not_fire_on_writer_full(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_writer_full_contract()
        self.assertFalse(any("SC-5" in w for w in warn_suspicious(c, "v3.6.6")))

    def test_sc5_does_not_fire_on_evaluator_full(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_evaluator_full_contract()
        self.assertFalse(any("SC-5" in w for w in warn_suspicious(c, "v3.6.6")))

    def test_sc11_does_not_fire_on_writer_full(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_writer_full_contract()
        self.assertFalse(any("SC-11" in w for w in warn_suspicious(c, "v3.6.6")))

    def test_sc11_does_not_fire_on_evaluator_full(self):
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_evaluator_full_contract()
        self.assertFalse(any("SC-11" in w for w in warn_suspicious(c, "v3.6.6")))

    def test_sc9_writer_full_reads_pre_commitment_artifacts_path(self):
        """SC-9 for writer_full should read pre_commitment_artifacts.acceptance_criteria_paraphrase.minimum_dimensions
        and fire when that integer exceeds dim count; not read measurement_procedure
        (which writer_full does not carry)."""
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_writer_full_contract()
        # 7 writer dimensions D1-D7 in shipped template; set minimum_dimensions to 99
        c["pre_commitment_artifacts"]["acceptance_criteria_paraphrase"]["minimum_dimensions"] = 99
        warnings = warn_suspicious(c, "v3.6.6")
        self.assertTrue(any("SC-9" in w and "pre_commitment_artifacts" in w for w in warnings))

    def test_sc9_evaluator_full_reads_disagreement_handling_path(self):
        """SC-9 for evaluator_full should read disagreement_handling.paraphrase_minimum_dimensions."""
        from scripts.check_sprint_contract import warn_suspicious
        c = _valid_evaluator_full_contract()
        c["disagreement_handling"]["paraphrase_minimum_dimensions"] = 99
        warnings = warn_suspicious(c, "v3.6.6")
        self.assertTrue(any("SC-9" in w and "disagreement_handling" in w for w in warnings))


if __name__ == "__main__":
    unittest.main()
