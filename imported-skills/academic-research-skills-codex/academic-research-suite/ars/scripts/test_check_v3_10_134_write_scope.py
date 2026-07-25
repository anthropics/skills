"""Mutation tests for check_v3_10_134_write_scope.py (the fail-open guard lint).

feedback_schema_mutation_test_for_constraints: after a lint passes on the real repo,
inject deliberately-broken state and assert the lint FAILS. A lint that passes on both
the clean repo AND a mutated repo is vacuous (trivially accept-all). Each test below
mutates one invariant's input and asserts a matching error surfaces.
"""

import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import check_v3_10_134_write_scope as lint  # noqa: E402


class CleanRepoTest(unittest.TestCase):
    def test_clean_repo_passes(self):
        # Baseline: the real repo state must pass (0 errors).
        self.assertEqual(lint.run_checks(), [])


class MutationTest(unittest.TestCase):
    """Each mutation must make run_checks() report at least one error."""

    def setUp(self):
        # snapshot the real loaders to restore after each mutation
        self._real_keys = lint.load_manifest_keys
        self._real_manifest = lint.load_manifest
        self._real_name = lint.read_frontmatter_name
        self._real_a = list(lint.BUCKET_A_AGENT_FILES)
        self._real_bcd = list(lint.BUCKET_BCD_AGENT_FILES)

    def tearDown(self):
        lint.load_manifest_keys = self._real_keys
        lint.load_manifest = self._real_manifest
        lint.read_frontmatter_name = self._real_name
        lint.BUCKET_A_AGENT_FILES = self._real_a
        lint.BUCKET_BCD_AGENT_FILES = self._real_bcd

    def _assert_fails(self, needle=None):
        errs = lint.run_checks()
        self.assertTrue(errs, "mutation should have produced at least one error")
        if needle:
            self.assertTrue(any(needle in e for e in errs),
                            f"expected an error mentioning {needle!r}; got {errs}")

    def test_I1_roster_size_drift_fails(self):
        # Drop one Bucket A agent from the roster -> size != 23.
        lint.BUCKET_A_AGENT_FILES = self._real_a[:-1]
        self._assert_fails("I1")

    def test_I2_manifest_missing_key_fails(self):
        # A real agent on disk has no manifest entry -> fail-open risk.
        real = self._real_keys()
        dropped = sorted(real)[0]
        lint.load_manifest_keys = lambda: real - {dropped}
        self._assert_fails("I2")

    def test_I2_manifest_typo_key_fails(self):
        # A manifest key that matches no on-disk name (rename/typo).
        real = self._real_keys()
        lint.load_manifest_keys = lambda: (real - {sorted(real)[0]}) | {"bibliografy_agent_typo"}
        self._assert_fails("I2")

    def test_I2_agent_renamed_on_disk_fails(self):
        # An agent file's frontmatter name drifts away from its manifest key.
        def fake_name(rel):
            if rel.endswith("bibliography_agent.md"):
                return "renamed_bibliography_agent"
            return self._real_name(rel)
        lint.read_frontmatter_name = fake_name
        self._assert_fails("I2")

    def test_I3_bcd_leak_into_manifest_fails(self):
        # A Bucket B agent's name (report_compiler_agent) appears as a manifest key.
        real = self._real_keys()
        lint.load_manifest_keys = lambda: real | {"report_compiler_agent"}
        errs = lint.run_checks()
        self.assertTrue(any("I3" in e for e in errs),
                        f"expected an I3 leak error; got {errs}")

    def test_I4_empty_globs_fails(self):
        real = self._real_manifest()
        import copy
        mutated = copy.deepcopy(real)
        first = sorted(mutated["agents"])[0]
        mutated["agents"][first]["allowed_write_globs"] = []
        lint.load_manifest = lambda: mutated
        self._assert_fails("I4")

    def test_I4_wrong_bucket_fails(self):
        real = self._real_manifest()
        import copy
        mutated = copy.deepcopy(real)
        first = sorted(mutated["agents"])[0]
        mutated["agents"][first]["bucket"] = "B"
        lint.load_manifest = lambda: mutated
        self._assert_fails("I4")

    def test_I5_undeclared_agent_on_disk_fails(self):
        # A real agent file dropped from BOTH rosters must be caught by the filesystem
        # exhaustiveness glob (NON-vacuous guard): the hook would fail OPEN for it.
        lint.BUCKET_A_AGENT_FILES = self._real_a[:-1]  # drop one Bucket A file from roster
        # (it still exists on disk, so I5's filesystem glob must flag it as undeclared)
        errs = lint.run_checks()
        self.assertTrue(any("I5" in e for e in errs),
                        f"expected an I5 undeclared-agent error; got {errs}")

    def test_I5_stale_roster_entry_fails(self):
        # A roster entry pointing at a non-existent file is a stale entry.
        lint.BUCKET_A_AGENT_FILES = self._real_a + ["deep-research/agents/ghost_agent.md"]
        errs = lint.run_checks()
        self.assertTrue(any("I5" in e for e in errs),
                        f"expected an I5 stale-entry error; got {errs}")


class I5DepthAndSymlinkTest(unittest.TestCase):
    """I5 must (a) catch an agent dir nested DEEPER than one level, and
    (b) NOT false-flag the plugin-root `agents/` mirror dir — real
    byte-identical copies since #413 (symlinks before that; both file kinds
    map back to the rostered deep-research source). Runs run_checks()
    against a synthetic REPO_ROOT so the real repo is untouched."""

    def setUp(self):
        self._real_root = lint.REPO_ROOT
        self._real_a = list(lint.BUCKET_A_AGENT_FILES)
        self._real_bcd = list(lint.BUCKET_BCD_AGENT_FILES)
        self._real_keys = lint.load_manifest_keys
        self._real_manifest = lint.load_manifest
        self._real_name = lint.read_frontmatter_name
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name).resolve()
        lint.REPO_ROOT = self.root

    def tearDown(self):
        lint.REPO_ROOT = self._real_root
        lint.BUCKET_A_AGENT_FILES = self._real_a
        lint.BUCKET_BCD_AGENT_FILES = self._real_bcd
        lint.load_manifest_keys = self._real_keys
        lint.load_manifest = self._real_manifest
        lint.read_frontmatter_name = self._real_name
        self._tmp.cleanup()

    def _write_agent(self, rel, name):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(f"---\nname: {name}\n---\nbody\n", encoding="utf-8")
        return p

    def _stub_loaders_to(self, a_files, bcd_files, manifest_keys):
        # Point every non-I5 invariant at consistent synthetic data so ONLY I5 can react.
        lint.BUCKET_A_AGENT_FILES = list(a_files)
        lint.BUCKET_BCD_AGENT_FILES = list(bcd_files)
        agents = {k: {"bucket": "A", "phase": "1", "allowed_write_globs": ["phase1_*/**"]}
                  for k in manifest_keys}
        lint.load_manifest = lambda: {"agents": agents}
        lint.load_manifest_keys = lambda: set(manifest_keys)

    def test_root_agents_materialized_copy_not_flagged(self):
        # #413: plugin-root agents/ holds REAL byte-identical copies (relative
        # symlinks broke Windows checkouts / zip installs). I5 maps a root
        # agents/ file to its deep-research/agents/<name> source BY NAME and
        # must not report it as undeclared — byte-equality with that source is
        # check_agents_mirror_sync.py's invariant, not I5's.
        real = self._write_agent("deep-research/agents/x_agent.md", "x_agent")
        agg = self.root / "agents"
        agg.mkdir()
        (agg / "x_agent.md").write_bytes(real.read_bytes())
        self._stub_loaders_to(["deep-research/agents/x_agent.md"], [], ["x_agent"])
        errs = lint.run_checks()
        self.assertFalse(any("I5" in e for e in errs),
                         f"root agents/ mirror copy must NOT be I5-undeclared; got {errs}")

    def test_root_agents_copy_without_rostered_source_is_flagged(self):
        # The name-mapping must not become a blanket allowlist: a file dropped
        # into root agents/ whose name maps to NO rostered deep-research
        # source is still the fail-open case I5 exists to catch.
        self._write_agent("deep-research/agents/x_agent.md", "x_agent")
        self._write_agent("agents/rogue_agent.md", "rogue_agent")
        self._stub_loaders_to(["deep-research/agents/x_agent.md"], [], ["x_agent"])
        errs = lint.run_checks()
        i5 = [e for e in errs if "I5" in e]
        self.assertTrue(any("rogue_agent" in e for e in i5),
                        f"unrostered root agents/ file must trigger I5; got {errs}")

    def test_root_agents_copy_of_non_deep_research_source_fails_closed(self):
        # The by-name mapping points ONLY at deep-research/agents/ — it must
        # not shadow-match a same-named rostered agent living elsewhere. A
        # mirror of e.g. academic-paper/agents/y_agent.md maps to the
        # (unrostered) deep-research path and is flagged: fail-CLOSED, which
        # is the documented lockstep-edit prompt, never a silent pass.
        real = self._write_agent("academic-paper/agents/y_agent.md", "y_agent")
        agg = self.root / "agents"
        agg.mkdir()
        (agg / "y_agent.md").write_bytes(real.read_bytes())
        self._stub_loaders_to(["academic-paper/agents/y_agent.md"], [], ["y_agent"])
        errs = lint.run_checks()
        i5 = [e for e in errs if "I5" in e]
        self.assertTrue(any("agents/y_agent.md" in e for e in i5),
                        f"non-deep-research mirror must fail closed; got {errs}")

    def test_nested_dir_under_root_agents_is_not_remapped(self):
        # codex review (#413 round, P2): the mirror remap applies ONLY to
        # DIRECT children of root agents/. A nested agents/sub/agents/x.md
        # whose NAME collides with a rostered deep-research agent must still
        # be flagged — remapping it would reopen the fail-open case the
        # recursive glob exists to catch.
        self._write_agent("deep-research/agents/x_agent.md", "x_agent")
        self._write_agent("agents/sub/agents/x_agent.md", "rogue")
        self._stub_loaders_to(["deep-research/agents/x_agent.md"], [], ["x_agent"])
        errs = lint.run_checks()
        i5 = [e for e in errs if "I5" in e]
        self.assertTrue(any("agents/sub/agents/x_agent.md" in e for e in i5),
                        f"nested file under root agents/ must not be remapped; got {errs}")

    def test_root_agents_symlink_aggregate_not_flagged(self):
        # Legacy/transition pin (pre-#413 file kind): a symlink in root
        # agents/ maps back the same way and must not be flagged.
        real = self._write_agent("deep-research/agents/x_agent.md", "x_agent")
        agg = self.root / "agents"
        agg.mkdir()
        try:
            os.symlink(real, agg / "x_agent.md")
        except OSError:
            self.skipTest("symlinks unavailable on this platform")
        # roster sizes are checked by I1; bypass that by patching the size expectation is not
        # possible, so just assert no I5 error specifically.
        self._stub_loaders_to(["deep-research/agents/x_agent.md"], [], ["x_agent"])
        errs = lint.run_checks()
        self.assertFalse(any("I5" in e for e in errs),
                         f"root agents/ symlink must NOT be I5-undeclared; got {errs}")

    def test_nested_agents_dir_undeclared_is_caught(self):
        # A genuinely new standalone agent file nested two levels deep, absent from the
        # roster, MUST be flagged — the one-level glob would have silently missed it.
        self._write_agent("deep-research/agents/x_agent.md", "x_agent")
        self._write_agent("skill/sub/agents/sneaky_agent.md", "sneaky_agent")  # nested, undeclared
        self._stub_loaders_to(["deep-research/agents/x_agent.md"], [], ["x_agent"])
        errs = lint.run_checks()
        i5 = [e for e in errs if "I5" in e]
        self.assertTrue(i5, f"nested undeclared agent must trigger I5; got {errs}")
        self.assertTrue(any("sneaky_agent" in e for e in i5),
                        f"I5 error should name the nested file; got {i5}")


if __name__ == "__main__":
    unittest.main()
