"""install-workflow.py must not downgrade a repo's vendored aec detector.

Row: https://app.notion.com/p/41a4efecc95a81388f71da096a699f71 (origin: nevar-integrations PR #11).
"""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SKILL = Path(__file__).resolve().parents[1]
INSTALLER = SKILL / "scripts" / "install-workflow.py"


def install(repo, *args):
    return subprocess.run([sys.executable, str(INSTALLER), *args], cwd=repo, capture_output=True, text=True)


class VendoredDetector(unittest.TestCase):
    def test_differing_repo_detector_is_left_untouched_even_with_force(self):
        with tempfile.TemporaryDirectory() as repo:
            dest = Path(repo) / "scripts" / "check-forged-gate-names.py"
            dest.parent.mkdir()
            dest.write_bytes(b"# newer aec copy\n")
            proc = install(repo, "--force")
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertEqual(dest.read_bytes(), b"# newer aec copy\n")
            self.assertIn("KEPT", proc.stderr)
            # everything else is still (re)installed
            self.assertEqual((Path(repo) / "scripts" / "check-forged-review-gate.py").read_bytes(),
                             (SKILL / "scripts" / "check-forged-review-gate.py").read_bytes())

    def test_known_older_vendored_detector_is_replaced_with_force(self):
        # #87 Codex P1: the 3.2.1-bundled detector (aec 46580fa) must be upgraded, not KEPT.
        import importlib.util
        spec = importlib.util.spec_from_file_location("iw", INSTALLER)
        iw = importlib.util.module_from_spec(spec); spec.loader.exec_module(iw)
        old = subprocess.run(["git", "show", "f599564b:review-gate/scripts/check-forged-gate-names.py"],
                             cwd=SKILL, capture_output=True)
        if old.returncode:
            self.skipTest("no git history (vendored layout)")
        import hashlib
        self.assertIn(hashlib.sha256(old.stdout).hexdigest(), iw.KNOWN_OLD)
        with tempfile.TemporaryDirectory() as repo:
            dest = Path(repo) / "scripts" / "check-forged-gate-names.py"
            dest.parent.mkdir()
            dest.write_bytes(old.stdout)
            proc = install(repo, "--force")
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertEqual(dest.read_bytes(), (SKILL / "scripts" / "check-forged-gate-names.py").read_bytes())
            self.assertNotIn("KEPT", proc.stderr)

    def test_byte_identical_detector_is_a_no_op(self):
        with tempfile.TemporaryDirectory() as repo:
            install(repo)
            dest = Path(repo) / "scripts" / "check-forged-gate-names.py"
            before = dest.stat().st_mtime_ns
            proc = install(repo, "--force")
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertIn("unchanged: " + str(dest.resolve()), proc.stdout)
            self.assertEqual(dest.stat().st_mtime_ns, before)

    def test_fresh_repo_gets_the_skill_copy(self):
        with tempfile.TemporaryDirectory() as repo:
            proc = install(repo)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertEqual((Path(repo) / "scripts" / "check-forged-gate-names.py").read_bytes(),
                             (SKILL / "scripts" / "check-forged-gate-names.py").read_bytes())
            self.assertNotIn("KEPT", proc.stderr)


if __name__ == "__main__":
    unittest.main()
