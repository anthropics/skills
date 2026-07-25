"""Unit tests for check_v3_9_2_phase_boundary.py."""
import subprocess
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script

SCRIPT = Path(__file__).resolve().parent / "check_v3_9_2_phase_boundary.py"


def _run() -> subprocess.CompletedProcess:
    return run_script(SCRIPT)


class CheckV392PhaseBoundaryTests(unittest.TestCase):

    def test_repo_baseline_passes(self) -> None:
        """The committed v3.9.2/v3.9.4 branch state must pass the lint."""
        result = _run()
        self.assertEqual(result.returncode, 0, msg=f"stderr: {result.stderr}")
        self.assertIn("PASSED", result.stdout)
        self.assertIn("23 Bucket A", result.stdout)
        self.assertIn("16 Bucket B/C/D", result.stdout)

    def test_module_invariants(self) -> None:
        """BUCKET counts must match classification doc (23 + 16 = 39)."""
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "check_v3_9_2_phase_boundary", SCRIPT
        )
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        self.assertEqual(len(module.BUCKET_A_AGENTS), 23)
        self.assertEqual(len(module.BUCKET_BCD_AGENTS), 16)
        # No agent appears in both buckets
        overlap = set(module.BUCKET_A_AGENTS) & set(module.BUCKET_BCD_AGENTS)
        self.assertEqual(overlap, set(), msg=f"agents in both buckets: {overlap}")
        # All 39 agent paths are unique (23 A + 16 BCD)
        all_paths = module.BUCKET_A_AGENTS + module.BUCKET_BCD_AGENTS
        self.assertEqual(len(all_paths), len(set(all_paths)),
                         msg="duplicate paths across buckets")

    def test_required_phrases_constant(self) -> None:
        """REQUIRED_PHRASES must include the version-neutral load-bearing markers.
        Version-specific markers (Phase Boundary, Enforcement) are handled via
        PHASE_BOUNDARY_RE / ENFORCEMENT_RE regexes (widened to v3.9.2|v3.9.4 in v3.9.4).
        """
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "check_v3_9_2_phase_boundary", SCRIPT
        )
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        required = set(module.REQUIRED_PHRASES)
        self.assertIn("MUST NOT", required)
        self.assertIn("MAY READ", required)
        # Version-specific markers are now regex-based
        self.assertTrue(
            hasattr(module, "PHASE_BOUNDARY_RE"),
            "PHASE_BOUNDARY_RE must exist (widened to v3.9.2|v3.9.4)"
        )
        self.assertTrue(
            hasattr(module, "ENFORCEMENT_RE"),
            "ENFORCEMENT_RE must exist (widened to v3.9.2|v3.9.4)"
        )
        # Both regexes must match either version
        self.assertIsNotNone(module.PHASE_BOUNDARY_RE.search("## Phase Boundary (v3.9.2)"))
        self.assertIsNotNone(module.PHASE_BOUNDARY_RE.search("## Phase Boundary (v3.9.4)"))
        self.assertIsNotNone(module.ENFORCEMENT_RE.search("Enforcement (v3.9.2)"))
        self.assertIsNotNone(module.ENFORCEMENT_RE.search("Enforcement (v3.9.4)"))

    def test_timeline_extraction_agent_in_bucket_a(self) -> None:
        """timeline_extraction_agent.md (v3.9.4) must be in BUCKET_A_AGENTS."""
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "check_v3_9_2_phase_boundary", SCRIPT
        )
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        self.assertIn(
            "deep-research/agents/timeline_extraction_agent.md",
            module.BUCKET_A_AGENTS,
            "timeline_extraction_agent.md must be in BUCKET_A_AGENTS (v3.9.4 Phase 2 sibling)"
        )


class CanonicalEnforcementDefriftTests(unittest.TestCase):
    """#491 defrift lock — the canonical enforcement sentence guard.

    Mutation discipline: every negative case drives the REAL check_bucket_a
    logic against a fixture file (module REPO_ROOT redirected to a tempdir),
    so a guard that silently stops matching cannot stay green.
    """

    STALE_SENTENCE = (
        "**Enforcement (v3.9.2):** prompt-level only. Advisory verifier "
        "(`scripts/check_pipeline_integrity.py`) can detect violations post-hoc. "
        "Deterministic PreToolUse hook deferred to v3.10 active conductor (#134)."
    )

    def _load_module(self):
        from tests.test_helpers import load_module_from_path
        return load_module_from_path("check_v3_9_2_phase_boundary", SCRIPT)

    def _block(self, enforcement_line: str, version: str = "2") -> str:
        return (
            f"## Phase Boundary (v3.9.{version})\n\n"
            "You MUST NOT write files in other phases.\n"
            "You MAY READ files in `phase1_*/`.\n\n"
            f"{enforcement_line}\n\n"
            "## Next Section\n"
        )

    def _check(self, module, content: str) -> list[str]:
        from tempfile import TemporaryDirectory
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture = root / "fixture_agent.md"
            fixture.write_text(content, encoding="utf-8")
            module.REPO_ROOT = root
            return module.check_bucket_a(fixture)

    def test_canonical_constants_shape(self) -> None:
        """Both version variants exist and carry their own version marker."""
        module = self._load_module()
        self.assertEqual(set(module.CANONICAL_ENFORCEMENT), {"2", "4"})
        self.assertIn("Enforcement (v3.9.2)", module.CANONICAL_ENFORCEMENT["2"])
        self.assertIn("Enforcement (v3.9.4)", module.CANONICAL_ENFORCEMENT["4"])
        self.assertIn("PR #294", module.CANONICAL_ENFORCEMENT["2"])

    def test_canonical_sentence_passes(self) -> None:
        module = self._load_module()
        errors = self._check(module, self._block(module.CANONICAL_ENFORCEMENT["2"]))
        self.assertEqual(errors, [])

    def test_canonical_with_file_specific_tail_passes(self) -> None:
        """Per-file tails after the canonical sentence stay free."""
        module = self._load_module()
        line = (module.CANONICAL_ENFORCEMENT["2"]
                + " The v3.6.2 Sprint Contract Protocol below ALSO applies.")
        errors = self._check(module, self._block(line))
        self.assertEqual(errors, [])

    def test_stale_pre_294_sentence_fails(self) -> None:
        """THE regression case: the pre-PR-#294 sentence that drifted repo-wide
        (audits/harness-retirement-2026-07-04.md B4-F01) must now fail."""
        module = self._load_module()
        errors = self._check(module, self._block(self.STALE_SENTENCE))
        self.assertEqual(len(errors), 1, msg=f"errors: {errors}")
        self.assertIn("drifted", errors[0])
        self.assertIn("#491", errors[0])

    def test_single_word_mutation_fails(self) -> None:
        module = self._load_module()
        mutated = module.CANONICAL_ENFORCEMENT["2"].replace(
            "write-scope guard", "write scope guard"
        )
        self.assertNotEqual(mutated, module.CANONICAL_ENFORCEMENT["2"])
        errors = self._check(module, self._block(mutated))
        self.assertEqual(len(errors), 1, msg=f"errors: {errors}")
        self.assertIn("drifted", errors[0])

    def test_version_mismatched_sentence_fails(self) -> None:
        """A v3.9.4 block carrying the v3.9.2 sentence is drift, not a pass."""
        module = self._load_module()
        errors = self._check(
            module,
            self._block(module.CANONICAL_ENFORCEMENT["2"], version="4"),
        )
        self.assertEqual(len(errors), 1, msg=f"errors: {errors}")
        self.assertIn("v3.9.4 variant", errors[0])

    def test_canonical_matches_repo_files(self) -> None:
        """The constants must match what actually ships in the agent files —
        a constant that drifts from disk would make the baseline test fail,
        but assert it directly for a precise failure message."""
        module = self._load_module()
        repo_root = Path(__file__).resolve().parent.parent
        v392_sample = (repo_root / "deep-research/agents/synthesis_agent.md").read_text(encoding="utf-8")
        v394_sample = (repo_root / "deep-research/agents/timeline_extraction_agent.md").read_text(encoding="utf-8")
        self.assertIn(module.CANONICAL_ENFORCEMENT["2"], v392_sample)
        self.assertIn(module.CANONICAL_ENFORCEMENT["4"], v394_sample)


if __name__ == "__main__":
    unittest.main()
