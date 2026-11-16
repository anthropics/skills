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

    def test_fresh_repo_gets_the_skill_copy(self):
        with tempfile.TemporaryDirectory() as repo:
            proc = install(repo)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertEqual((Path(repo) / "scripts" / "check-forged-gate-names.py").read_bytes(),
                             (SKILL / "scripts" / "check-forged-gate-names.py").read_bytes())
            self.assertNotIn("KEPT", proc.stderr)


if __name__ == "__main__":
    unittest.main()
