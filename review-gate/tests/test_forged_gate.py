"""Behavior tests for the forged-`Review Gate` step (SEC-MVS-01 S5).

Runs the workflow template's real `run:` block under bash with a fake `gh` on PATH,
so a regression in the wiring (not only in the detector) fails here.
"""
import base64
import json
import os
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SKILL = Path(__file__).resolve().parents[1]
SCRIPTS = SKILL / "scripts"
TEMPLATE = SKILL / "templates" / "review-gate.yml"
TRUSTED_RUN = ".github/workflows/review-gate.yml\tpull_request_target"

FAKE_GH = r'''#!/usr/bin/env python3
import base64, json, os, sys
state = os.environ["FAKE_STATE"]
args = sys.argv[1:]
with open(os.path.join(state, "calls.log"), "a") as log:
    log.write(" ".join(args) + "\n")
fixture = json.load(open(os.path.join(state, "fixture.json")))
path = next(a for a in args if a.startswith("repos/"))
if "-X" in args and "POST" in args:
    print(41); sys.exit(0)
if "-X" in args and "PATCH" in args:
    concl = next(a.split("=", 1)[1] for a in args if a.startswith("conclusion="))
    open(os.path.join(state, "conclusion"), "w").write(concl); sys.exit(0)
if "/contents/scripts/" in path:
    name = path.split("/contents/scripts/")[1].split("?")[0]
    src = fixture["scripts"].get(name)
    if src is None:
        sys.exit(1)
    print(json.dumps({"content": base64.b64encode(open(src, "rb").read()).decode()})); sys.exit(0)
if "/check-runs" in path and "/commits/" in path:
    if fixture.get("listing_fails"):
        sys.exit(1)
    print(json.dumps({"total_count": len(fixture["check_runs"]), "check_runs": fixture["check_runs"]})); sys.exit(0)
if "/actions/runs/" in path:
    run_id = path.rsplit("/", 1)[1]
    if run_id not in fixture["runs"]:
        sys.exit(1)
    print(fixture["runs"][run_id]); sys.exit(0)
sys.exit(3)
'''


def run_block():
    lines = TEMPLATE.read_text().splitlines()
    start = next(i for i, l in enumerate(lines) if l.strip() == "run: |") + 1
    indent = len(lines[start]) - len(lines[start].lstrip())
    body = []
    for line in lines[start:]:
        if line.strip() and len(line) - len(line.lstrip()) < indent:
            break
        body.append(line)
    return textwrap.dedent("\n".join(body)) + "\n"


def job(name, run_id):
    return {"name": name, "details_url": f"https://github.com/o/r/actions/runs/{run_id}/job/9{run_id}",
            "html_url": f"https://github.com/o/r/actions/runs/{run_id}/job/9{run_id}"}


def api_check(name, check_id):
    return {"name": name, "details_url": f"https://github.com/o/r/runs/{check_id}",
            "html_url": f"https://github.com/o/r/runs/{check_id}"}


class ForgedGateWorkflow(unittest.TestCase):
    def gate(self, check_runs, runs=None, listing_fails=False, missing=()):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            bindir = tmp / "bin"; bindir.mkdir()
            (bindir / "gh").write_text(FAKE_GH); (bindir / "gh").chmod(0o755)
            passing_checker = tmp / "check-review-gate.py"
            passing_checker.write_text("print('review-gate ok')\n")
            scripts = {"check-review-gate.py": str(passing_checker),
                       "check-forged-gate-names.py": str(SCRIPTS / "check-forged-gate-names.py"),
                       "check-forged-review-gate.py": str(SCRIPTS / "check-forged-review-gate.py")}
            for name in missing:
                scripts.pop(name)
            (tmp / "fixture.json").write_text(json.dumps(
                {"scripts": scripts, "check_runs": check_runs, "runs": runs or {}, "listing_fails": listing_fails}))
            workdir = tmp / "job"; workdir.mkdir()
            env = dict(os.environ, PATH=f"{bindir}:{os.environ['PATH']}", FAKE_STATE=str(tmp), GH_TOKEN="x",
                       PR_NUMBER="7", REPO="o/r", SHA="a" * 40, DEFAULT_BRANCH="main")
            # The block writes the trusted scripts to /tmp/<name>; point that at this test's own dir.
            script = run_block().replace("/tmp/", f"{workdir}/")
            proc = subprocess.run(["bash", "-e", "-c", script], env=env, capture_output=True, text=True)
            concl = (tmp / "conclusion").read_text() if (tmp / "conclusion").exists() else None
            return proc.returncode, concl, proc.stdout + proc.stderr

    def test_forged_same_repo_review_gate_job_fails_the_gate(self):
        rc, concl, out = self.gate(
            [api_check("Review Gate", 41), job("Review Gate", 500)],
            runs={"500": ".github/workflows/forge.yml\tpull_request"})
        self.assertEqual((rc, concl), (1, "failure"), out)
        self.assertIn("forged check 'Review Gate'", out)

    def test_trusted_workflow_job_and_checks_api_run_pass(self):
        rc, concl, out = self.gate(
            [api_check("Review Gate", 41), job("Review Gate", 501), job("CI", 502)],
            runs={"501": TRUSTED_RUN, "502": ".github/workflows/ci.yml\tpull_request"})
        self.assertEqual((rc, concl), (0, "success"), out)

    def test_main_via_staging_pull_request_job_is_not_flagged(self):
        # Several repos publish this name from a plain pull_request job; Review Gate must not block them.
        rc, concl, out = self.gate(
            [job("PRs into main must come from staging", 503)],
            runs={"503": ".github/workflows/main-via-staging.yml\tpull_request"})
        self.assertEqual((rc, concl), (0, "success"), out)

    def test_failed_listing_fails_closed(self):
        rc, concl, out = self.gate([], listing_fails=True)
        self.assertEqual((rc, concl), (1, "failure"), out)

    def test_unreadable_run_lookup_fails_closed(self):
        rc, concl, out = self.gate([job("Review Gate", 504)], runs={})
        self.assertEqual((rc, concl), (1, "failure"), out)
        self.assertIn("forged-check step failed (exit 2)", out)

    def test_missing_detector_on_default_branch_fails_closed(self):
        rc, concl, out = self.gate([], missing=("check-forged-gate-names.py",))
        self.assertEqual((rc, concl), (1, "failure"), out)
        self.assertIn("Missing trusted scripts/check-forged-gate-names.py", out)


class WrapperReason(unittest.TestCase):
    def test_wrapper_reason_still_holds(self):
        # The wrapper exists only because the vendored map protects this name with no trusted pair.
        # If a re-vendor changes that, revisit (or delete) the wrapper.
        import importlib.util
        spec = importlib.util.spec_from_file_location("cfgn", SCRIPTS / "check-forged-gate-names.py")
        detector = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(detector)
        self.assertEqual(detector.PROTECTED["PRs into main must come from staging"], set())
        self.assertEqual(detector.PROTECTED["Review Gate"],
                         {(".github/workflows/review-gate.yml", "pull_request_target")})
        header = (SCRIPTS / "check-forged-review-gate.py").read_text()
        self.assertIn("WHY THIS WRAPPER EXISTS", header)
        self.assertIn("DELETE THIS WRAPPER when Option A or B", header)


class CopMergeCommand(unittest.TestCase):
    def test_documented_command_never_runs_the_pr_checkout(self):
        # A PR controls its checkout's scripts/, so the cop's merge-time run must use the installed skill.
        doc = (SKILL.parent / "pr-merge-flow" / "SKILL.md").read_text()
        runs = [l for l in doc.splitlines() if "python3" in l and "check-forged-review-gate.py" in l]
        self.assertTrue(runs)
        for line in runs:
            self.assertIn("python3 ~/.claude/skills/review-gate/scripts/check-forged-review-gate.py", line)
            self.assertNotRegex(line, r"python3 (\./)?scripts/")


class InstalledCopies(unittest.TestCase):
    def test_repo_copies_match_skill_copies(self):
        # This repo's own gate loads scripts/ and .github/workflows/ from main; keep them the skill's copies.
        root = SKILL.parent
        for name in ("check-forged-gate-names.py", "check-forged-review-gate.py"):
            self.assertEqual((root / "scripts" / name).read_bytes(), (SCRIPTS / name).read_bytes(), name)
        self.assertEqual((root / ".github/workflows/review-gate.yml").read_bytes(), TEMPLATE.read_bytes())


if __name__ == "__main__":
    unittest.main()
