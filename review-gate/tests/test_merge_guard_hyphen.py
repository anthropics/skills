"""merge-guard must not treat a hyphenated word like `pr-merge-flow` as `pr ... merge`.

Runs the real hook in a subprocess (test_check_review_gate.py monkeypatches the module globally).
Row: https://app.notion.com/p/41a4efecc95a81fba79fd4d79b23bf92
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

GUARD = Path(__file__).resolve().parents[1] / "scripts" / "merge-guard.py"


# Keep the hook's best-effort feedback logging away from the real feedback store.
_HOME = tempfile.mkdtemp(prefix="rg-hook-home-")
ENV = {k: v for k, v in os.environ.items() if k not in ("AGENT_FEEDBACK_BIN", "CLAUDE_PROJECT_DIR")}
ENV.update(HOME=_HOME, CLAUDE_PROJECT_DIR=_HOME)


def hook(cmd, tool="Bash", raw=None, argv=None):
    payload = {"tool_name": tool, "tool_input": {"command": cmd}, "cwd": tempfile.gettempdir()}
    proc = subprocess.run(argv or [sys.executable, str(GUARD)], input=raw if raw is not None else json.dumps(payload),
                          capture_output=True, text=True, timeout=60, env=ENV)
    return proc.returncode, proc.stderr


class AnyShellToolName(unittest.TestCase):
    def test_merge_blocks_under_any_tool_name(self):
        for tool in ("Bash", "mcp__skin_target__garment_Bash", "run_shell_command", "BashTool", ""):
            with self.subTest(tool=tool):
                self.assertEqual(hook("gh pr merge 5 --squash", tool=tool)[0], 2)

    def test_no_command_passes_and_unreadable_input_blocks(self):
        self.assertEqual(hook("", tool="Edit")[0], 0)
        self.assertEqual(hook("", raw="not json")[0], 2)
        self.assertEqual(hook("", raw="[1]")[0], 2)

    def test_crash_fails_closed(self):
        # ~1000-deep `$( … )` nest: RecursionError used to exit 1, a non-blocking hook error, so the merge ran.
        n = 1000
        cmd = "echo " + "$( echo " * (n - 1) + "$( gh pr merge 5 -R o/r )" + " )" * (n - 1)
        rc, err = hook(cmd)
        self.assertEqual(rc, 2, err[-300:])
        self.assertIn("crashed (RecursionError); blocked", err)

    def test_crash_with_failing_feedback_log_still_blocks(self):
        # fb_log raising inside the crash handler (Path.home() → RuntimeError) must not turn the block into exit 1.
        n = 1000
        cmd = "echo " + "$( echo " * (n - 1) + "$( gh pr merge 5 -R o/r )" + " )" * (n - 1)
        code = ("import pathlib, runpy, sys\n"
                "def _boom(*a, **k): raise RuntimeError('no home')\n"
                "pathlib.Path.home = classmethod(_boom)\n"
                f"runpy.run_path({str(GUARD)!r}, run_name='__main__')\n")
        rc, err = hook(cmd, argv=[sys.executable, "-c", code])
        self.assertEqual(rc, 2, err[-300:])
        self.assertIn("crashed (RecursionError); blocked", err)

    def test_missing_gate_module_blocks(self):
        # merge-guard copied without check-review-gate.py (half-applied upgrade): import failure must exit 2.
        d = tempfile.mkdtemp(prefix="rg-lonely-")
        try:
            shutil.copy(GUARD, d)
            rc, err = hook("gh pr merge 5 --squash", argv=[sys.executable, str(Path(d) / GUARD.name)])
        finally:
            shutil.rmtree(d)
        self.assertEqual(rc, 2, err[-300:])
        self.assertIn("cannot load check-review-gate.py", err)

    def test_input_and_cmd_aliases_are_checked(self):
        for payload in ({"input": {"command": "gh pr merge 5 --squash"}},
                        {"tool_input": {"cmd": "gh pr merge 5 --squash"}}):
            with self.subTest(payload=payload):
                self.assertEqual(hook("", raw=json.dumps({**payload, "cwd": tempfile.gettempdir()}))[0], 2)


class HyphenatedMentions(unittest.TestCase):
    def test_mention_only_commands_pass(self):
        for cmd in ['grep -rn pr-merge-flow . "$@"',
                    'ls ~/.claude/skills/pr-merge-flow "$@"',
                    'set -- pr-merge-flow; echo "$@"',
                    'args=(pr-merge-flow docs); ls "${args[@]}"',
                    "aec install skill pr-merge-flow </dev/null"]:
            with self.subTest(cmd=cmd):
                rc, err = hook(cmd)
                self.assertEqual(rc, 0, err)

    def test_real_merges_still_block(self):
        for cmd in ['set -- pr merge 5; gh "$@"',
                    'args=(pr merge 5); gh "${args[@]}"',
                    "g''h pr merge 5 --squash",
                    'g"h" pr merge 5',
                    "gh pr merge 5 --squash"]:
            with self.subTest(cmd=cmd):
                rc, err = hook(cmd)
                self.assertEqual(rc, 2, f"not blocked: {cmd}\n{err}")


if __name__ == "__main__":
    unittest.main()
