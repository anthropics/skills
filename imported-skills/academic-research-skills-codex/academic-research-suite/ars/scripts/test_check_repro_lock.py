"""Unit tests for check_repro_lock.py."""
import subprocess
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
import textwrap

from tests.test_helpers import run_script

SCRIPT = Path(__file__).resolve().parent / "check_repro_lock.py"


def _run(path: Path) -> subprocess.CompletedProcess:
    return run_script(SCRIPT, str(path))


def _valid_passport_yaml() -> str:
    return textwrap.dedent("""\
        origin_skill: deep-research
        origin_mode: full
        origin_date: "2026-04-15T10:00:00Z"
        verification_status: VERIFIED
        version_label: "v1.0"
        repro_lock:
          schema_version: "1.0"
          stochasticity_declaration: "LLM outputs are not byte-reproducible. This lockfile documents configuration, not a deterministic replay guarantee."
          ars_version: "3.3.5"
          model:
            family: claude
            id: claude-opus-4-7
            weight_stable: false
          prompts:
            hash_timing: skill-load
            skill_md_hash: "sha256:abc123"
            agents_bundle_hash: "sha256:def456"
          materials:
            list_hash: "sha256:ghi789"
            count: 12
          external_protocols:
            s2_api_protocol_version: "3.3"
            s2_snapshot_available: false
          cross_model:
            enabled: false
            secondary_model_id: null
        """)


class TestReproLock(unittest.TestCase):
    def test_valid_block_passes(self) -> None:
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "passport.yaml"
            p.write_text(_valid_passport_yaml())
            result = _run(p)
            self.assertEqual(result.returncode, 0, msg=result.stderr + result.stdout)

    def test_null_repro_lock_passes_with_warning(self) -> None:
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "passport.yaml"
            y = _valid_passport_yaml().split("repro_lock:")[0] + "repro_lock: null\n"
            p.write_text(y)
            result = _run(p)
            self.assertEqual(result.returncode, 0)
            # WARN signal must reach at least stderr; stdout OK line also mentions WARN
            self.assertIn("WARN", result.stderr)
            self.assertIn("with WARN", result.stdout)

    def test_missing_key_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "passport.yaml"
            y = _valid_passport_yaml().split("repro_lock:")[0]  # strip the key entirely
            p.write_text(y)
            result = _run(p)
            self.assertEqual(result.returncode, 1)
            self.assertIn("repro_lock", result.stdout)

    def test_missing_subfield_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "passport.yaml"
            y = _valid_passport_yaml().replace('ars_version: "3.3.5"\n  ', '')
            p.write_text(y)
            result = _run(p)
            self.assertEqual(result.returncode, 1)
            self.assertIn("ars_version", result.stdout)

    def test_unknown_schema_version_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "passport.yaml"
            y = _valid_passport_yaml().replace('schema_version: "1.0"', 'schema_version: "9.9"')
            p.write_text(y)
            result = _run(p)
            self.assertEqual(result.returncode, 1)
            self.assertIn("schema_version", result.stdout)

    def test_missing_stochasticity_declaration_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            p = Path(tmp) / "passport.yaml"
            y = _valid_passport_yaml()
            # Remove the stochasticity_declaration line
            lines = [l for l in y.splitlines() if "stochasticity_declaration" not in l]
            p.write_text("\n".join(lines) + "\n")
            result = _run(p)
            self.assertEqual(result.returncode, 1)
            self.assertIn("stochasticity_declaration", result.stdout)


if __name__ == "__main__":
    unittest.main()
