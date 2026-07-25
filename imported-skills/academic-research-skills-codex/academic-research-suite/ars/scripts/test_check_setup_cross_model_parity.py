"""Unit tests for check_setup_cross_model_parity.py (#491 fold-in)."""
import unittest
from pathlib import Path

from tests.test_helpers import load_module_from_path, run_script

SCRIPT = Path(__file__).resolve().parent / "check_setup_cross_model_parity.py"

EN_OK = 'export ARS_CROSS_MODEL="gpt-5.5"\n# or: export ARS_CROSS_MODEL="gemini-3.1-pro-preview"\n'
ZH_OK = EN_OK
CANONICAL_OK = (
    "| Model | API ID | Provider |\n"
    "|-------|--------|----------|\n"
    "| GPT-5.5 | `gpt-5.5` | OpenAI |\n"
    "| Gemini 3.1 Pro | `gemini-3.1-pro-preview` | Google |\n"
    "\n"
    "(`gpt-5.4` / `gpt-5.4-pro` remain accepted for existing setups.)\n"
)


def _load_module():
    return load_module_from_path("check_setup_cross_model_parity", SCRIPT)


class SetupCrossModelParityTests(unittest.TestCase):

    def test_repo_baseline_passes(self) -> None:
        """The committed SETUP + canonical doc state must pass."""
        result = run_script(SCRIPT)
        self.assertEqual(result.returncode, 0, msg=f"stderr: {result.stderr}")
        self.assertIn("PASSED", result.stdout)

    def test_clean_fixture_passes(self) -> None:
        module = _load_module()
        self.assertEqual(module.check(EN_OK, ZH_OK, CANONICAL_OK), [])

    def test_en_zh_drift_fails(self) -> None:
        """One-sided edit (the B4-F02 shape: en updated, zh-TW forgotten)."""
        module = _load_module()
        zh_stale = 'export ARS_CROSS_MODEL="gpt-5.4-pro"\n'
        errors = module.check(EN_OK, zh_stale, CANONICAL_OK)
        self.assertTrue(any("drift" in e for e in errors), msg=f"errors: {errors}")

    def test_legacy_id_in_prose_note_does_not_count(self) -> None:
        """codex P1 regression (PR #492): `gpt-5.4-pro` is backticked in the
        canonical doc's legacy-accepted NOTE but absent from the model tables —
        a SETUP example reverting to it must FAIL, not pass on the note."""
        module = _load_module()
        stale = 'export ARS_CROSS_MODEL="gpt-5.4-pro"\n'
        errors = module.check(stale, stale, CANONICAL_OK)
        self.assertTrue(
            any("gpt-5.4-pro" in e and "not in" in e for e in errors),
            msg=f"errors: {errors}",
        )

    def test_canonical_table_parse_fails_closed(self) -> None:
        """No 'API ID' table in the canonical doc = parser stale = error."""
        module = _load_module()
        errors = module.check(EN_OK, ZH_OK, "prose only, `gpt-5.5` backticked")
        self.assertTrue(
            any("parser went stale" in e for e in errors), msg=f"errors: {errors}"
        )

    def test_compat_table_column_counts(self) -> None:
        """Ids in the compat table's 'Example API ID(s)' column are members."""
        module = _load_module()
        canonical = CANONICAL_OK + (
            "\n| Provider | Example API ID(s) | Endpoint |\n"
            "|----------|-------------------|----------|\n"
            "| DeepSeek | `deepseek-v4-pro` | https://api.deepseek.com/v1 |\n"
        )
        ids = module.canonical_model_ids(canonical)
        self.assertIn("deepseek-v4-pro", ids)
        self.assertNotIn("gpt-5.4-pro", ids)

    def test_wildcard_prefix_tokens_are_not_ids(self) -> None:
        """codex P2 regression (PR #492): the compat table's "any
        non-`gpt-*`/`gemini-*` id" prose sits in an API ID column — globs are
        prefix patterns, not model ids, and a SETUP example of `gpt-*` must
        fail, not pass on the leaked token."""
        module = _load_module()
        canonical = CANONICAL_OK + (
            "\n| Provider | Example API ID(s) | Endpoint |\n"
            "|----------|-------------------|----------|\n"
            "| Any OpenAI-compatible | any non-`gpt-*`/`gemini-*` id | any |\n"
        )
        self.assertNotIn("gpt-*", module.canonical_model_ids(canonical))
        glob_setup = 'export ARS_CROSS_MODEL="gpt-*"\n'
        errors = module.check(glob_setup, glob_setup, canonical)
        self.assertTrue(
            any("gpt-*" in e and "not in" in e for e in errors),
            msg=f"errors: {errors}",
        )

    def test_unknown_model_fails(self) -> None:
        """Example naming a model outside the canonical lineup."""
        module = _load_module()
        bad = 'export ARS_CROSS_MODEL="gpt-9.9-imaginary"\n'
        errors = module.check(bad, bad, CANONICAL_OK)
        self.assertTrue(
            any("gpt-9.9-imaginary" in e and "canonical" in e for e in errors),
            msg=f"errors: {errors}",
        )

    def test_zero_examples_fails_closed(self) -> None:
        """Regex-went-stale / block-removed must be an error, not a pass."""
        module = _load_module()
        errors = module.check("no examples here", ZH_OK, CANONICAL_OK)
        self.assertTrue(
            any("Fail-closed" in e for e in errors), msg=f"errors: {errors}"
        )

    def test_commented_example_lines_are_extracted(self) -> None:
        """`# or:` alternates count — they are user-pasteable examples too."""
        module = _load_module()
        ids = module.extract_ids(EN_OK)
        self.assertEqual(ids, ["gpt-5.5", "gemini-3.1-pro-preview"])


if __name__ == "__main__":
    unittest.main()
