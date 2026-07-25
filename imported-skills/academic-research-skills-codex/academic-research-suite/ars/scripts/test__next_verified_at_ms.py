"""Unit tests for scripts/_next_verified_at_ms.py (ARS v3.6.7 Step 6 Phase 6.4).

Per spec §5.4 strict-monotonic helper:

  def _next_verified_at_ms(passport_audit_artifacts: list) -> str:
      now_ms = utc_now_ms()
      if not passport_audit_artifacts:
          return now_ms
      latest_ms = max(entry["verdict"]["verified_at"] for entry in passport_audit_artifacts)
      return max(now_ms, increment_ms(latest_ms, 1))

§10 Phase 6.4 verification gate: "_next_verified_at_ms() always returns a
string strictly greater than every prior verified_at; verified by
property-based test."

Cases per §10:
  (a) empty ledger
  (b) clock fresh (now > latest+1ms)
  (c) clock stale (now <= latest, helper bumps by 1 ms)
  (d) multiple prior entries (max selected, not last)

Plus property-based monotonic test and RFC 3339 ms shape test.
"""
from __future__ import annotations

import re
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import Any
from unittest.mock import patch

from scripts._next_verified_at_ms import (
    bump_ms,
    next_verified_at_ms,
    parse_rfc3339_ms,
    rfc3339_ms,
    utc_now_ms,
)
from tests.test_helpers import run_script

REPO = Path(__file__).resolve().parent.parent
SCRIPT = REPO / "scripts/_next_verified_at_ms.py"

RFC3339_MS_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d{3}Z$")


def _persisted_entry(verified_at: str) -> dict[str, Any]:
    return {
        "stage": 2,
        "agent": "synthesis_agent",
        "deliverable_path": "x.md",
        "deliverable_sha": "a" * 64,
        "run_id": "2026-04-30T15-22-04Z-d8f3",
        "bundle_manifest_sha": "9" * 64,
        "artifact_paths": {
            "jsonl": "x.jsonl",
            "sidecar": "x.meta.json",
            "verdict": "x.verdict.yaml",
        },
        "verdict": {
            "status": "MINOR",
            "round": 1,
            "target_rounds": 3,
            "finding_counts": {"p1": 0, "p2": 0, "p3": 1},
            "verified_at": verified_at,
            "verified_by": "pipeline_orchestrator_agent",
        },
    }


class TestNextVerifiedAtMs(unittest.TestCase):
    """Pure-function behaviour per §5.4 / §10 cases (a)-(d)."""

    # Case (a)
    def test_empty_ledger_returns_now(self) -> None:
        with patch("scripts._next_verified_at_ms.utc_now_ms", return_value="2026-04-30T15:30:00.000Z"):
            self.assertEqual(next_verified_at_ms([]), "2026-04-30T15:30:00.000Z")

    # Case (b)
    def test_clock_fresh_returns_now(self) -> None:
        prior = [_persisted_entry("2026-04-30T15:22:04.123Z")]
        with patch("scripts._next_verified_at_ms.utc_now_ms", return_value="2026-04-30T15:30:00.000Z"):
            self.assertEqual(next_verified_at_ms(prior), "2026-04-30T15:30:00.000Z")

    # Case (c)
    def test_clock_stale_bumps_latest_by_one_ms(self) -> None:
        prior = [_persisted_entry("2026-04-30T15:30:00.000Z")]
        with patch("scripts._next_verified_at_ms.utc_now_ms", return_value="2026-04-30T15:30:00.000Z"):
            self.assertEqual(next_verified_at_ms(prior), "2026-04-30T15:30:00.001Z")

    def test_clock_behind_bumps_latest_by_one_ms(self) -> None:
        prior = [_persisted_entry("2026-04-30T15:30:00.000Z")]
        with patch("scripts._next_verified_at_ms.utc_now_ms", return_value="2026-04-30T15:29:59.500Z"):
            self.assertEqual(next_verified_at_ms(prior), "2026-04-30T15:30:00.001Z")

    # Case (d)
    def test_multi_entries_picks_max_not_last(self) -> None:
        prior = [
            _persisted_entry("2026-04-30T15:22:04.123Z"),
            _persisted_entry("2026-04-30T15:50:00.999Z"),
            _persisted_entry("2026-04-30T15:30:00.000Z"),
        ]
        with patch("scripts._next_verified_at_ms.utc_now_ms", return_value="2026-04-30T15:30:00.000Z"):
            self.assertEqual(next_verified_at_ms(prior), "2026-04-30T15:50:01.000Z")

    def test_ms_overflow_carries_to_seconds(self) -> None:
        prior = [_persisted_entry("2026-04-30T15:22:04.999Z")]
        with patch("scripts._next_verified_at_ms.utc_now_ms", return_value="2026-04-30T15:22:04.000Z"):
            self.assertEqual(next_verified_at_ms(prior), "2026-04-30T15:22:05.000Z")

    def test_returns_rfc3339_ms_shape(self) -> None:
        with patch("scripts._next_verified_at_ms.utc_now_ms", return_value="2026-04-30T15:30:00.000Z"):
            result = next_verified_at_ms([])
        self.assertRegex(result, RFC3339_MS_RE)


class TestStrictMonotonicProperty(unittest.TestCase):
    """§10 verification gate: result strictly greater than every prior entry."""

    def test_property_strictly_greater_than_every_prior(self) -> None:
        scenarios: list[tuple[list[str], str]] = [
            ([], "2026-04-30T15:30:00.000Z"),
            (["2026-04-30T15:30:00.000Z"], "2026-04-30T15:30:00.000Z"),
            (["2026-04-30T15:30:00.500Z"], "2026-04-30T15:30:00.000Z"),
            (["2026-04-30T15:30:00.000Z"], "2026-04-30T16:00:00.000Z"),
            (
                ["2026-04-30T15:22:04.123Z", "2026-04-30T15:50:00.999Z", "2026-04-30T15:30:00.000Z"],
                "2026-04-30T15:30:00.000Z",
            ),
            (["2026-04-30T15:22:04.999Z"], "2026-04-30T15:22:04.000Z"),
        ]
        for prior_strs, now in scenarios:
            with self.subTest(prior=prior_strs, now=now):
                prior = [_persisted_entry(s) for s in prior_strs]
                with patch("scripts._next_verified_at_ms.utc_now_ms", return_value=now):
                    result = next_verified_at_ms(prior)
                result_ms = parse_rfc3339_ms(result)
                for s in prior_strs:
                    self.assertGreater(
                        result_ms,
                        parse_rfc3339_ms(s),
                        f"result {result} not > prior {s}",
                    )


class TestPrimitives(unittest.TestCase):
    """parse_rfc3339_ms / rfc3339_ms / bump_ms round-trip and edge cases."""

    def test_parse_round_trip(self) -> None:
        for s in [
            "2026-04-30T15:22:04.123Z",
            "2026-04-30T15:22:04.000Z",
            "2026-04-30T23:59:59.999Z",
        ]:
            with self.subTest(s=s):
                self.assertEqual(rfc3339_ms(parse_rfc3339_ms(s)), s)

    def test_bump_ms_overflows_second(self) -> None:
        self.assertEqual(
            rfc3339_ms(bump_ms(parse_rfc3339_ms("2026-04-30T15:22:04.999Z"), 1)),
            "2026-04-30T15:22:05.000Z",
        )

    def test_bump_ms_overflows_minute(self) -> None:
        self.assertEqual(
            rfc3339_ms(bump_ms(parse_rfc3339_ms("2026-04-30T15:22:59.999Z"), 1)),
            "2026-04-30T15:23:00.000Z",
        )

    def test_utc_now_ms_real_clock_shape(self) -> None:
        # Sanity: real clock returns the expected shape.
        self.assertRegex(utc_now_ms(), RFC3339_MS_RE)

    def test_parse_rejects_non_ms_format(self) -> None:
        for s in [
            "2026-04-30T15:22:04Z",
            "2026-04-30T15:22:04.12Z",
            "2026-04-30T15:22:04.1234Z",
            "2026-04-30 15:22:04.123Z",
            "2026-04-30T15:22:04.123+00:00",
        ]:
            with self.subTest(s=s):
                with self.assertRaises(ValueError):
                    parse_rfc3339_ms(s)


class TestCli(unittest.TestCase):
    """CLI invocation per §10 Phase 6.4 deliverables (--passport <path>)."""

    def test_cli_with_empty_passport_yaml_returns_now_shape(self) -> None:
        with TemporaryDirectory() as td:
            passport = Path(td) / "passport.yaml"
            passport.write_text("audit_artifact: []\n", encoding="utf-8")
            result = run_script(SCRIPT, "--passport", str(passport))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertRegex(result.stdout.strip(), RFC3339_MS_RE)

    def test_cli_with_prior_entries_returns_strictly_greater(self) -> None:
        with TemporaryDirectory() as td:
            passport = Path(td) / "passport.yaml"
            passport.write_text(
                "audit_artifact:\n"
                "  - verdict:\n"
                "      verified_at: '2099-12-31T23:59:58.000Z'\n"
                "  - verdict:\n"
                "      verified_at: '2026-01-01T00:00:00.000Z'\n",
                encoding="utf-8",
            )
            result = run_script(SCRIPT, "--passport", str(passport))
        self.assertEqual(result.returncode, 0, result.stderr)
        out = result.stdout.strip()
        self.assertRegex(out, RFC3339_MS_RE)
        self.assertGreater(parse_rfc3339_ms(out), parse_rfc3339_ms("2099-12-31T23:59:58.000Z"))

    def test_cli_with_unquoted_timestamps_does_not_crash(self) -> None:
        # Spec §3.1 example uses unquoted timestamps. PyYAML's default loader
        # would coerce these to datetime objects and break parse_rfc3339_ms.
        # CLI must keep them as strings (BaseLoader path).
        with TemporaryDirectory() as td:
            passport = Path(td) / "passport.yaml"
            passport.write_text(
                "audit_artifact:\n"
                "  - verdict:\n"
                "      verified_at: 2099-12-31T23:59:58.000Z\n",
                encoding="utf-8",
            )
            result = run_script(SCRIPT, "--passport", str(passport))
        self.assertEqual(result.returncode, 0, result.stderr)
        out = result.stdout.strip()
        self.assertRegex(out, RFC3339_MS_RE)
        self.assertGreater(parse_rfc3339_ms(out), parse_rfc3339_ms("2099-12-31T23:59:58.000Z"))

    def test_cli_with_no_audit_artifact_key_returns_now(self) -> None:
        with TemporaryDirectory() as td:
            passport = Path(td) / "passport.yaml"
            passport.write_text("schema_version: 9\n", encoding="utf-8")
            result = run_script(SCRIPT, "--passport", str(passport))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertRegex(result.stdout.strip(), RFC3339_MS_RE)

    def test_cli_missing_passport_exits_nonzero(self) -> None:
        result = run_script(SCRIPT, "--passport", "/no/such/file.yaml")
        self.assertNotEqual(result.returncode, 0)

    def test_cli_malformed_yaml_exits_two(self) -> None:
        with TemporaryDirectory() as td:
            passport = Path(td) / "passport.yaml"
            passport.write_text("audit_artifact: [\n  unbalanced", encoding="utf-8")
            result = run_script(SCRIPT, "--passport", str(passport))
        self.assertEqual(result.returncode, 2)
        self.assertIn("failed to parse", result.stderr)


if __name__ == "__main__":
    unittest.main()
