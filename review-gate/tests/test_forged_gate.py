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
created_path = os.path.join(state, "created.json")
created = json.load(open(created_path)) if os.path.exists(created_path) else []
if "-X" in args and "POST" in args:
    check_id = 900 + len(created)
    created.append({"id": check_id, "name": "Review Gate", "app": {"slug": "github-actions"},
                    "details_url": f"https://github.com/o/r/runs/{check_id}"})
    json.dump(created, open(created_path, "w")); print(check_id); sys.exit(0)
if "-X" in args and "PATCH" in args:
    concl = next(a.split("=", 1)[1] for a in args if a.startswith("conclusion="))
    with open(os.path.join(state, "patches.log"), "a") as patches:
        patches.write(f"{path.rsplit('/', 1)[1]} {concl}\n")
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
    runs = fixture["check_runs"] + created
    print(json.dumps({"total_count": len(runs), "check_runs": runs})); sys.exit(0)
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
    return {"id": 9000 + run_id, "name": name, "app": {"slug": "github-actions"}, "details_url": f"https://github.com/o/r/actions/runs/{run_id}/job/9{run_id}",
            "html_url": f"https://github.com/o/r/actions/runs/{run_id}/job/9{run_id}"}


def api_check(name, check_id):
    return {"id": check_id, "name": name, "app": {"slug": "github-actions"}, "details_url": f"https://github.com/o/r/runs/{check_id}",
            "html_url": f"https://github.com/o/r/runs/{check_id}"}


class ForgedGateWorkflow(unittest.TestCase):
    def gate(self, check_runs, runs=None, listing_fails=False, missing=(), evaluations=1):
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
            for _ in range(evaluations):
                proc = subprocess.run(["bash", "-e", "-c", script], env=env, capture_output=True, text=True)
            concl = (tmp / "conclusion").read_text() if (tmp / "conclusion").exists() else None
            self.calls = (tmp / "calls.log").read_text().splitlines()
            self.patches = (tmp / "patches.log").read_text().splitlines() if (tmp / "patches.log").exists() else []
            self.created = json.loads((tmp / "created.json").read_text()) if (tmp / "created.json").exists() else []
            return proc.returncode, concl, proc.stdout + proc.stderr

    def test_forged_same_repo_review_gate_job_fails_the_gate(self):
        rc, concl, out = self.gate(
            [api_check("Review Gate", 41), job("Review Gate", 500)],
            runs={"500": ".github/workflows/forge.yml\tpull_request"})
        self.assertEqual((rc, concl), (1, "failure"), out)
        self.assertIn("forged check 'Review Gate'", out)

    def test_checks_api_run_and_other_jobs_pass(self):
        rc, concl, out = self.gate(
            [api_check("Review Gate", 41), job("review-gate-runner", 501), job("CI", 502)],
            runs={"501": TRUSTED_RUN, "502": ".github/workflows/ci.yml\tpull_request"})
        self.assertEqual((rc, concl), (0, "success"), out)

    def test_stacked_child_review_gate_job_on_head_fails_the_gate(self):
        # H is the outer PR's head and the stacked child's base: the child's pull_request_target job
        # attaches to H with the trusted path/event pair. It must not count as this PR's gate.
        rc, concl, out = self.gate([api_check("Review Gate", 41), job("Review Gate", 505)],
                                   runs={"505": TRUSTED_RUN})
        self.assertEqual((rc, concl), (1, "failure"), out)
        self.assertIn("forged check 'Review Gate'", out)

    def test_gate_job_is_not_named_like_the_required_check(self):
        # The real result is the Checks API run; an Actions job named "Review Gate" would land on the
        # base SHA, which is a stacked child's head-or-base. Every Actions-created "Review Gate" is forged.
        jobs = TEMPLATE.read_text().split("\njobs:\n", 1)[1]
        self.assertNotIn("name: Review Gate", jobs)

    def test_main_via_staging_pull_request_job_is_not_flagged(self):
        # Several repos publish this name from a plain pull_request job; Review Gate must not block them.
        rc, concl, out = self.gate(
            [job("PRs into main must come from staging", 503)],
            runs={"503": ".github/workflows/main-via-staging.yml\tpull_request"})
        self.assertEqual((rc, concl), (0, "success"), out)

    # 3.2.1: GitHub blocks the PR while any `Review Gate` run in the suite is red, so each
    # evaluation must reuse the head's run instead of POSTing another next to an old failure.
    def test_two_publishes_leave_exactly_one_run(self):
        rc, concl, out = self.gate([job("CI", 502)], runs={"502": ".github/workflows/ci.yml\tpull_request"},
                                   evaluations=2)
        self.assertEqual((rc, concl), (0, "success"), out)
        self.assertEqual([c["id"] for c in self.created], [900], self.calls)
        self.assertEqual(sum(1 for c in self.calls if "-X POST" in c), 1, self.calls)
        self.assertEqual(self.patches[-1], "900 success")

    def test_every_existing_api_run_is_completed_and_none_is_added(self):
        # #85's head: three API runs in one suite, two red from evaluations before Codex finished.
        rc, concl, out = self.gate([api_check("Review Gate", 41), api_check("Review Gate", 42),
                                    api_check("Review Gate", 43)])
        self.assertEqual((rc, concl), (0, "success"), out)
        self.assertEqual(self.created, [])
        self.assertEqual(self.patches[-3:], ["41 success", "42 success", "43 success"])

    def test_same_named_actions_job_is_never_reused(self):
        # A PR job named "Review Gate" is forged; the gate must not adopt or PATCH it.
        rc, concl, out = self.gate([job("Review Gate", 500)],
                                   runs={"500": ".github/workflows/forge.yml\tpull_request"})
        self.assertEqual((rc, concl), (1, "failure"), out)
        self.assertEqual([c["id"] for c in self.created], [900])
        self.assertEqual({p.split()[0] for p in self.patches}, {"900"})

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
        self.assertIn('detector.PROTECTED = {"Review Gate": set()}', header)
        self.assertIn("NO TRUSTED ACTIONS PAIR FOR `Review Gate`", header)
        self.assertIn("WHY THIS WRAPPER EXISTS", header)
        self.assertIn("DELETE THIS WRAPPER when Option A or B", header)


class WrapperDetector(unittest.TestCase):
    def wrapper(self, check_runs, runs):
        with tempfile.TemporaryDirectory() as tmp:
            bindir = Path(tmp); (bindir / "gh").write_text(FAKE_GH); (bindir / "gh").chmod(0o755)
            (bindir / "fixture.json").write_text(json.dumps({"scripts": {}, "check_runs": check_runs, "runs": runs}))
            env = dict(os.environ, PATH=f"{bindir}:{os.environ['PATH']}", FAKE_STATE=tmp, REPO="o/r")
            stdin = json.dumps({"total_count": len(check_runs), "check_runs": check_runs})
            proc = subprocess.run([sys.executable, str(SCRIPTS / "check-forged-review-gate.py")], input=stdin,
                                  env=env, capture_output=True, text=True)
            return proc.returncode, proc.stderr

    def test_stacked_child_success_beside_failed_outer_gate_exits_1(self):
        # The cop's merge-time run: outer gate (Checks API) failed, child's trusted-pair job succeeded on H.
        failed_outer = dict(api_check("Review Gate", 41), conclusion="failure")
        child = dict(job("Review Gate", 506), conclusion="success")
        rc, err = self.wrapper([failed_outer, child], {"506": TRUSTED_RUN})
        self.assertEqual(rc, 1, err)

    def test_checks_api_publication_alone_exits_0(self):
        rc, err = self.wrapper([api_check("Review Gate", 41)], {})
        self.assertEqual(rc, 0, err)


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
