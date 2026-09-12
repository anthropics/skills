#!/usr/bin/env python3
"""Smoke tests for the ServiceNow helper and bundled references."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
HELPER_PATH = ROOT / "scripts" / "snow_helper.py"

spec = importlib.util.spec_from_file_location("snow_helper", HELPER_PATH)
snow_helper = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = snow_helper
spec.loader.exec_module(snow_helper)


class QueryGenerationTests(unittest.TestCase):
    def test_group_names_with_apostrophes_are_preserved(self) -> None:
        query = snow_helper.generate_query("find all incidents assigned to group Bob's Team")
        self.assertIn("assignment_group.name", query)
        self.assertIn("Bob\\'s Team", query)

    def test_last_n_days_query_uses_valid_add_query_signature(self) -> None:
        query = snow_helper.generate_query("find all incidents created in the last 7 days")
        self.assertIn("gr.addQuery('sys_created_on', '>=', gs.daysAgoStart(7));", query)

    def test_count_query_uses_glide_aggregate(self) -> None:
        query = snow_helper.generate_query("count active incidents")
        self.assertIn("new GlideAggregate('incident')", query)
        self.assertIn("ga.addAggregate('COUNT');", query)

    def test_security_incident_mapping_is_available(self) -> None:
        query = snow_helper.generate_query("find all security incidents in state containment")
        self.assertIn("new GlideRecord('sn_si_incident')", query)

    def test_sam_pro_mapping_is_available(self) -> None:
        query = snow_helper.generate_query("find all software entitlements in state active")
        self.assertIn("new GlideRecord('alm_license')", query)


class LintTests(unittest.TestCase):
    def test_detects_direct_assignment_for_any_gliderecord_variable(self) -> None:
        issues = snow_helper.lint_script(
            "var ticket = new GlideRecord('incident');\n"
            "ticket.short_description = 'Hello';\n"
        )
        self.assertTrue(any("Direct field assignment" in issue.message for issue in issues))

    def test_detects_unfiltered_query(self) -> None:
        issues = snow_helper.lint_script(
            "var gr = new GlideRecord('incident');\n"
            "gr.query();\n"
        )
        self.assertTrue(any("without any filter conditions" in issue.message for issue in issues))

    def test_detects_add_aggregate_on_gliderecord(self) -> None:
        issues = snow_helper.lint_script(
            "var gr = new GlideRecord('incident');\n"
            "gr.addAggregate('COUNT');\n"
        )
        self.assertTrue(any("addAggregate()" in issue.message for issue in issues))

    def test_integrationhub_template_is_available(self) -> None:
        class Args:
            table = "incident"

        template = snow_helper.template_integrationhub_action(Args())
        self.assertIn("Connection & Credential Alias", template)
        self.assertIn("RESTMessageV2", template)


class ValidationTests(unittest.TestCase):
    def test_skill_validation_passes(self) -> None:
        errors = snow_helper.validate_skill(str(ROOT))
        self.assertEqual([], errors)


if __name__ == "__main__":
    unittest.main()
