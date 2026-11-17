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


DETECTOR = (SKILL / "scripts" / "check-forged-gate-names.py").read_bytes()
SIGNATURE = b"def forged(check_runs, run_lookup, protected=None):"
assert SIGNATURE in DETECTOR
# a newer/custom detector the bundled wrapper runs against
COMPATIBLE = b"# newer aec copy\n" + DETECTOR
# #105 Codex P2: these define every name the wrapper uses, yet the wrapper cannot run against them
INCOMPATIBLE = DETECTOR.replace(SIGNATURE, b"def forged(check_runs, run_lookup):")  # old 2-arg forged
INCOMPATIBLE_VARIANTS = (
    INCOMPATIBLE,
    b"# custom\nPROTECTED = {}\ndef forged(c, l, protected=None): return []\n"
    b"def _gh_run_lookup(repo): return None\ndef _load_check_runs(text): return []\n",  # no Review Gate entry
    b"# old custom detector\nPROTECTED = {}\ndef forged(c, l): return []\n",
    b"def broken(:\n",
    DETECTOR.replace(SIGNATURE, b"def forged(check_runs, run_lookup, protected=None, *, audit):"),  # required kw-only
)


class VendoredDetector(unittest.TestCase):
    def test_incompatible_custom_detector_refuses_without_force(self):
        # 3.2.8 P2: a KEPT detector the upgraded wrapper cannot use would fail every gate run
        with tempfile.TemporaryDirectory() as repo:
            dest = Path(repo) / "scripts" / "check-forged-gate-names.py"
            dest.parent.mkdir()
            for variant in INCOMPATIBLE_VARIANTS:
                with self.subTest(variant=variant[:40]):
                    dest.write_bytes(variant)
                    proc = install(repo)
                    self.assertEqual(proc.returncode, 1, proc.stderr)
                    self.assertIn("cannot run against", proc.stderr)
                    self.assertEqual(dest.read_bytes(), variant)
                    self.assertFalse((Path(repo) / "scripts" / "check-forged-review-gate.py").exists())
                    self.assertFalse((Path(repo) / ".github").exists())

    def test_the_installer_never_executes_the_repo_detector(self):
        # #105 Codex P1: compatibility is decided by parsing; repo code never runs on install
        with tempfile.TemporaryDirectory() as repo, tempfile.TemporaryDirectory() as side:
            marker = Path(side) / "ran"
            dest = Path(repo) / "scripts" / "check-forged-gate-names.py"
            dest.parent.mkdir()
            for body in (b"open(%r, 'w').close()\nraise SystemExit(0)\n" % str(marker).encode(),
                         COMPATIBLE + b"\nopen(%r, 'w').close()\n" % str(marker).encode()):
                with self.subTest(body=body[:30]):
                    dest.write_bytes(body)
                    install(repo)
                    install(repo, "--force")
                    self.assertFalse(marker.exists())

    def test_incompatible_custom_detector_is_backed_up_and_replaced_with_force(self):
        with tempfile.TemporaryDirectory() as repo:
            dest = Path(repo) / "scripts" / "check-forged-gate-names.py"
            dest.parent.mkdir()
            dest.write_bytes(INCOMPATIBLE)
            proc = install(repo, "--force")
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertEqual(dest.read_bytes(), (SKILL / "scripts" / dest.name).read_bytes())
            self.assertEqual(dest.with_name(dest.name + ".custom.bak").read_bytes(), INCOMPATIBLE)
            self.assertIn("REPLACED", proc.stderr)

    def test_a_second_forced_replacement_keeps_the_first_backup(self):
        # #105 Codex P2: the first custom copy must survive a later forced upgrade of a second one
        with tempfile.TemporaryDirectory() as repo:
            dest = Path(repo) / "scripts" / "check-forged-gate-names.py"
            dest.parent.mkdir()
            first, second = INCOMPATIBLE_VARIANTS[1], INCOMPATIBLE_VARIANTS[2]
            dest.write_bytes(first)
            self.assertEqual(install(repo, "--force").returncode, 0)
            dest.write_bytes(second)
            proc = install(repo, "--force")
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertEqual(dest.with_name(dest.name + ".custom.bak").read_bytes(), first)
            self.assertEqual(dest.with_name(dest.name + ".custom.1.bak").read_bytes(), second)


    def test_differing_repo_detector_is_left_untouched_even_with_force(self):
        with tempfile.TemporaryDirectory() as repo:
            dest = Path(repo) / "scripts" / "check-forged-gate-names.py"
            dest.parent.mkdir()
            dest.write_bytes(COMPATIBLE)
            proc = install(repo, "--force")
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertEqual(dest.read_bytes(), COMPATIBLE)
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
