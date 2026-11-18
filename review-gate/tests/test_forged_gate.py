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

import yaml

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
fail = fixture.get("fail")  # {"pattern": regex over the joined args, "nth": which match 404s (1-based)}
if fail and __import__("re").search(fail["pattern"], " ".join(args)):
    seen_path = os.path.join(state, "fail.count")
    seen = int(open(seen_path).read()) + 1 if os.path.exists(seen_path) else 1
    open(seen_path, "w").write(str(seen))
    if seen == fail.get("nth", 1):
        print("gh: Not Found (HTTP 404)", file=sys.stderr); sys.exit(1)
HEAD = "a" * 40
created_path = os.path.join(state, "created.json")
created = json.load(open(created_path)) if os.path.exists(created_path) else []
if "-X" in args and "POST" in args:
    check_id = 900 + len(created)
    ext = next((a.split("=", 1)[1] for a in args if a.startswith("external_id=")), None)
    created.append({"id": check_id, "name": "Review Gate", "app": {"slug": "github-actions"},
                    "external_id": ext, "details_url": f"https://github.com/o/r/runs/{check_id}",
                    "check_suite": {"id": fixture.get("current_suite", 1)}})
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
    runs = fixture["check_runs"] + created + fixture.get("own_jobs", [])
    page2 = fixture.get("page2", [])  # served only to --paginate, as a second concatenated page
    print(json.dumps({"total_count": len(runs) + len(page2), "check_runs": runs}))
    if page2 and "--paginate" in args:
        print(json.dumps({"total_count": len(runs) + len(page2), "check_runs": page2}))
    sys.exit(0)
if "/actions/runs/" in path and ".display_title" in args:  # the wrapper's run-title provenance lookup
    run_id = path.rsplit("/", 1)[1]
    if run_id not in fixture.get("titles", {}):
        sys.exit(1)
    print(fixture["titles"][run_id]); sys.exit(0)
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


def api_check(name, check_id, pr=None, suite=1):
    return {"id": check_id, "name": name, "app": {"slug": "github-actions"}, "details_url": f"https://github.com/o/r/runs/{check_id}",
            "html_url": f"https://github.com/o/r/runs/{check_id}", "external_id": f"review-gate-pr-{pr}" if pr else None,
            "check_suite": {"id": suite}}


def run_title(pr):
    """The workflow run title GitHub shows for PR <pr>: the template's run-name as YAML parses it."""
    return str(yaml.safe_load(TEMPLATE.read_text())["run-name"]).replace(
        "${{ github.event.pull_request.number }}", str(pr))


RG_PATH = ".github/workflows/review-gate.yml"


class ForgedGateWorkflow(unittest.TestCase):
    def gate(self, check_runs, runs=None, listing_fails=False, missing=(), evaluations=1, prs=None, fixture=None, empty=()):
        """prs: [(pr_number, checker_rc)] evaluations on the same head sha (default PR 7 passing).

        Each evaluation's own job (`Review Gate`, run 600 + n) is on the head, as GitHub lists it.
        """
        prs = prs or [("7", 0)] * evaluations
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            bindir = tmp / "bin"; bindir.mkdir()
            (bindir / "gh").write_text(FAKE_GH); (bindir / "gh").chmod(0o755)
            passing_checker = tmp / "check-review-gate.py"
            passing_checker.write_text("import os, sys\nprint('review-gate ok')\nsys.exit(int(os.environ['FAKE_CHECKER_RC']))\n")
            scripts = {"check-review-gate.py": str(passing_checker),
                       "check-forged-gate-names.py": str(SCRIPTS / "check-forged-gate-names.py"),
                       "check-forged-review-gate.py": str(SCRIPTS / "check-forged-review-gate.py")}
            for name in missing:
                scripts.pop(name)
            for name in empty:
                (tmp / f"empty-{name}").write_text("")
                scripts[name] = str(tmp / f"empty-{name}")
            own_ids = [str(600 + n) for n, _ in enumerate(prs)]
            (tmp / "fixture.json").write_text(json.dumps(
                {"scripts": scripts, "check_runs": check_runs, "listing_fails": listing_fails,
                 "runs": {**{i: TRUSTED_RUN for i in own_ids}, **(runs or {})},
                 "titles": {i: run_title(n) for i, (n, _) in zip(own_ids, prs)},
                 "own_jobs": [job("Review Gate", int(i)) for i in own_ids], **(fixture or {})}))
            workdir = tmp / "job"; workdir.mkdir()
            env = dict(os.environ, PATH=f"{bindir}:{os.environ['PATH']}", FAKE_STATE=str(tmp), GH_TOKEN="x",
                       PR_NUMBER="7", REPO="o/r", SHA="a" * 40, DEFAULT_BRANCH="main")
            # The block writes the trusted scripts to /tmp/<name>; point that at this test's own dir.
            script = run_block().replace("/tmp/", f"{workdir}/")
            self.rcs = []
            for pr_number, checker_rc in prs:
                proc = subprocess.run(["bash", "-e", "-c", script], capture_output=True, text=True,
                                      env=dict(env, PR_NUMBER=pr_number, FAKE_CHECKER_RC=str(checker_rc)))
                self.rcs.append(proc.returncode)
            self.calls = (tmp / "calls.log").read_text().splitlines()
            self.patches = (tmp / "patches.log").read_text().splitlines() if (tmp / "patches.log").exists() else []
            self.created = json.loads((tmp / "created.json").read_text()) if (tmp / "created.json").exists() else []
            return proc.returncode, proc.stdout + proc.stderr

    def final(self):
        out = {}
        for line in self.patches:
            check_id, conclusion = line.split()
            out[check_id] = conclusion
        return out

    def test_forged_same_repo_review_gate_job_fails_the_gate(self):
        rc, out = self.gate([job("Review Gate", 500)], runs={"500": ".github/workflows/forge.yml\tpull_request"})
        self.assertEqual(rc, 1, out)
        self.assertIn("forged check 'Review Gate'", out)

    def test_own_job_and_other_jobs_pass(self):
        rc, out = self.gate([job("CI", 502)], runs={"502": ".github/workflows/ci.yml\tpull_request"})
        self.assertEqual(rc, 0, out)

    def test_failing_checker_fails_the_job(self):
        rc, out = self.gate([])
        self.assertEqual(rc, 0, out)
        rc, out = self.gate([], prs=[("7", 1)])
        self.assertEqual(rc, 1, out)

    # 3.2.8: the job IS the required check. Its check run is on the PR head in its own run's suite
    # (email_demo #1068), the suite the required-status rule reads; a Checks API POST lands in the head's
    # oldest suite and the rule read "expected" (#104). So the job carries the name and nothing is POSTed.
    def test_gate_job_is_named_like_the_required_check(self):
        self.assertEqual(yaml.safe_load(TEMPLATE.read_text())["jobs"]["gate"]["name"], "Review Gate")

    def test_no_check_run_is_posted(self):
        self.assertNotIn("-X POST", run_block())
        self.gate([api_check("Review Gate", 41, pr=7)])
        self.assertEqual(self.created, [])
        self.assertFalse([c for c in self.calls if "POST" in c], self.calls)

    def test_main_via_staging_pull_request_job_is_not_flagged(self):
        # Several repos publish this name from a plain pull_request job; Review Gate must not block them.
        rc, out = self.gate([job("PRs into main must come from staging", 503)],
                            runs={"503": ".github/workflows/main-via-staging.yml\tpull_request"})
        self.assertEqual(rc, 0, out)

    # 3.2.1 still holds for runs 3.2.0-3.2.7 POSTed: every evaluation completes all of this PR's legacy
    # API runs with its result, so no earlier red (or green) API run stays standing beside the job.
    def test_every_legacy_api_run_of_this_pr_gets_the_latest_result(self):
        legacy = [api_check("Review Gate", 41, pr=7), api_check("Review Gate", 42, pr=7)]
        rc, out = self.gate(legacy, prs=[("7", 0), ("7", 1)])
        self.assertEqual(rc, 1, out)
        self.assertEqual(self.final(), {"41": "failure", "42": "failure"})
        self.gate(legacy, prs=[("7", 1), ("7", 0)])
        self.assertEqual(self.final(), {"41": "success", "42": "success"})

    # nevar-content Codex P1: two PRs on one head sha must not complete each other's legacy runs. Each
    # also sees the other's gate job on the head, so both fail closed (3.2.8): only 41 ever gets PR 11's.
    def test_shared_head_pr_b_never_flips_pr_a_legacy_run(self):
        self.gate([api_check("Review Gate", 41, pr=11), api_check("Review Gate", 42, pr=12)],
                  prs=[("11", 1), ("12", 0)])
        self.assertEqual(self.rcs, [1, 1])
        self.assertEqual(self.final(), {"41": "failure", "42": "failure"})

    def test_unmarked_or_other_pr_runs_and_jobs_are_never_patched(self):
        # Pre-3.2.2 runs carry no PR marker: they could belong to any PR on this head, so never adopt them.
        rc, out = self.gate([api_check("Review Gate", 41), api_check("Review Gate", 42, pr=8),
                             job("Review Gate", 500)], runs={"500": ".github/workflows/forge.yml\tpull_request"})
        self.assertEqual(rc, 1, out)
        self.assertEqual(self.patches, [])

    # #105 Codex P1: another PR on this head (open, merged, or closed-unmerged, which commits/{sha}/pulls
    # omits) leaves a trusted-pair job here. Its run title names that PR, so it is not this PR's result.
    def test_another_prs_gate_job_on_this_head_fails_the_gate(self):
        rc, out = self.gate([job("Review Gate", 517)], runs={"517": TRUSTED_RUN},
                            fixture={"titles": {"600": run_title(7), "517": run_title(8)}})
        self.assertEqual(rc, 1, out)
        self.assertIn("'Review Gate - PR #8', not 'Review Gate - PR #7'", out)
        self.assertFalse([c for c in self.calls if "/pulls" in c], self.calls)  # no PR listing to fool

    def test_failed_listing_fails_closed(self):
        rc, out = self.gate([], listing_fails=True)
        self.assertEqual(rc, 1, out)

    def test_unreadable_run_lookup_fails_closed(self):
        rc, out = self.gate([job("Review Gate", 504)])
        self.assertEqual(rc, 1, out)
        self.assertIn("forged-check step failed (exit 2)", out)

    def test_empty_trusted_script_fails_closed(self):
        for name in ("check-review-gate.py", "check-forged-review-gate.py"):
            with self.subTest(name=name):
                rc, out = self.gate([], empty=(name,))
                self.assertEqual(rc, 1, out)
                self.assertIn(f"Could not load trusted scripts/{name}", out)

    def test_missing_detector_on_default_branch_fails_closed(self):
        rc, out = self.gate([], missing=("check-forged-gate-names.py",))
        self.assertEqual(rc, 1, out)
        self.assertIn("Could not load trusted scripts/check-forged-gate-names.py", out)
        self.assertIn("::error::review-gate: gh api GET repos/o/r/contents/scripts/check-forged-gate-names.py?ref=main failed", out)

    # nevar-auth #26 (3.2.7): a PATCH got "gh: Not Found (HTTP 404)", the step died without naming the call,
    # and its POSTed run stayed queued. 3.2.8 POSTs nothing; any API error fails the job, which IS the
    # check (a terminal failure even with the Checks API down), and the log names method and endpoint.
    # Legacy cleanup stays best effort: the failed job, not the legacy run, is what blocks the merge.
    def api_error(self, pattern, nth=1, prs=None):
        rc, out = self.gate([api_check("Review Gate", 41, pr=7)], prs=prs,
                            fixture={"fail": {"pattern": pattern, "nth": nth}})
        self.assertEqual(rc, 1, out)
        return out

    def test_initial_legacy_patch_error_fails_before_evaluating(self):
        out = self.api_error(r"PATCH repos/o/r/check-runs/41 ")
        self.assertIn("::error::review-gate: gh api PATCH repos/o/r/check-runs/41 failed (exit 1)", out)
        self.assertFalse([c for c in self.calls if "/contents/" in c], self.calls)

    def test_final_legacy_patch_error_turns_a_pass_into_a_failure(self):
        out = self.api_error(r"PATCH repos/o/r/check-runs/41 ", nth=2)
        self.assertIn("::error::review-gate: gh api PATCH repos/o/r/check-runs/41 failed (exit 1)", out)
        self.assertIn("were not all completed; failing closed", out)
        self.assertEqual(self.patches, ["41 failure"])

    def test_legacy_listing_error_fails_closed_and_names_the_call(self):
        out = self.api_error(r"check_name=Review%20Gate")
        self.assertIn("::error::review-gate: gh api GET repos/o/r/commits/" + "a" * 40
                      + "/check-runs?check_name=Review%20Gate&filter=all&per_page=100 failed", out)
        self.assertIn("could not list legacy Review Gate check runs", out)
        self.assertEqual(self.patches, [])

    def test_final_legacy_listing_error_fails_a_passing_gate(self):
        out = self.api_error(r"check_name=Review%20Gate", nth=2)
        self.assertIn("could not list legacy Review Gate check runs", out)
        self.assertEqual(self.patches, ["41 failure"])

    def test_forged_listing_error_names_the_call(self):
        out = self.api_error(r"check-runs\?per_page=100&filter=all")
        self.assertIn("::error::review-gate: gh api GET repos/o/r/commits/" + "a" * 40
                      + "/check-runs?per_page=100&filter=all failed", out)
        self.assertEqual(self.final(), {"41": "failure"})

    # Sonnet b on ea4fb8b, P1 1: both listings must read every page, not only the first 100 runs.
    def test_forged_job_on_a_later_page_fails_the_gate(self):
        rc, out = self.gate([], runs={"500": ".github/workflows/forge.yml\tpull_request"},
                            fixture={"page2": [job("Review Gate", 500)]})
        self.assertEqual(rc, 1, out)
        self.assertIn("forged check 'Review Gate'", out)

    def test_legacy_run_on_a_later_page_is_completed(self):
        rc, out = self.gate([], fixture={"page2": [api_check("Review Gate", 41, pr=7)]})
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.final(), {"41": "success"})

    # Sonnet b on ea4fb8b, P1 2-3: the trigger, token scope and step inputs are the security boundary.
    def test_trigger_permissions_and_inputs_are_pinned(self):
        wf = yaml.safe_load(TEMPLATE.read_text())
        self.assertEqual(wf[True], {"pull_request_target": {"types": [
            "opened", "reopened", "ready_for_review", "synchronize", "edited", "labeled", "unlabeled"]}})
        self.assertEqual(wf["permissions"], {"contents": "read", "pull-requests": "read", "checks": "write",
                                             "actions": "read"})
        # no concurrency group: a cancelled newest run blocks the merge (review-gate-sandbox PR #30)
        self.assertNotIn("concurrency", wf)
        self.assertNotIn("concurrency", wf["jobs"]["gate"])
        self.assertEqual(list(wf["jobs"]), ["gate"])
        (step,) = wf["jobs"]["gate"]["steps"]
        self.assertEqual(step["env"], {
            "GH_TOKEN": "${{ secrets.GITHUB_TOKEN }}",
            "PR_NUMBER": "${{ github.event.pull_request.number }}",
            "REPO": "${{ github.repository }}",
            "SHA": "${{ github.event.pull_request.head.sha }}",
            "DEFAULT_BRANCH": "${{ github.event.repository.default_branch }}"})
        self.assertNotIn("uses", step)  # no checkout: PR-head code never runs

    # 3.2.7 P1: an unquoted run-name lost " #<n>" to a YAML comment. Parse the real template, as GitHub does.
    def test_run_name_keeps_the_pr_number(self):
        self.assertEqual(run_title(7), "Review Gate - PR #7")
        wrapper = (SCRIPTS / "check-forged-review-gate.py").read_text()
        self.assertIn(f'RUN_TITLE = "{run_title("{pr}")}"', wrapper)  # the wrapper matches this exact title
        for line in TEMPLATE.read_text().split("\njobs:\n", 1)[0].splitlines():  # top-level plain scalars
            if line and not line[0].isspace() and not line.startswith("#") and ": " in line:
                value = line.split(": ", 1)[1].strip()
                self.assertFalse(" #" in value and value[0] not in "\"'", line)


class WrapperReason(unittest.TestCase):
    def test_wrapper_reason_still_holds(self):
        # The wrapper exists only because the vendored map protects the other name with no trusted pair.
        # If a re-vendor changes that, revisit (or delete) the wrapper.
        import importlib.util
        spec = importlib.util.spec_from_file_location("cfgn", SCRIPTS / "check-forged-gate-names.py")
        detector = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(detector)
        self.assertEqual(detector.PROTECTED["PRs into main must come from staging"], set())
        self.assertEqual(detector.PROTECTED["Review Gate"],
                         {(".github/workflows/review-gate.yml", "pull_request_target")})
        header = (SCRIPTS / "check-forged-review-gate.py").read_text()
        self.assertIn("THE GATE'S OWN JOB IS THE RESULT", header)
        self.assertIn("WHY THIS WRAPPER EXISTS", header)
        self.assertIn("DELETE THIS WRAPPER when Option A or B", header)


class WrapperDetector(unittest.TestCase):
    def wrapper(self, check_runs, runs, stdin=None, fixture=None, **env_over):
        with tempfile.TemporaryDirectory() as tmp:
            bindir = Path(tmp); (bindir / "gh").write_text(FAKE_GH); (bindir / "gh").chmod(0o755)
            (bindir / "fixture.json").write_text(json.dumps({
                "scripts": {}, "check_runs": check_runs, "runs": runs,
                "titles": {i: run_title(7) for i in runs}, **(fixture or {})}))
            env = dict(os.environ, PATH=f"{bindir}:{os.environ['PATH']}", FAKE_STATE=tmp, REPO="o/r", PR_NUMBER="7")
            for key, value in env_over.items():
                if value is None:
                    env.pop(key, None)
                else:
                    env[key] = value
            if stdin is None:
                stdin = json.dumps({"total_count": len(check_runs), "check_runs": check_runs})
            proc = subprocess.run([sys.executable, str(SCRIPTS / "check-forged-review-gate.py")], input=stdin,
                                  env=env, capture_output=True, text=True)
            return proc.returncode, proc.stderr

    def test_gate_job_from_the_trusted_pair_exits_0(self):
        # Includes a pre-3.2.0 workflow's `Review Gate` job: same pair, also the real gate result.
        rc, err = self.wrapper([job("Review Gate", 506), api_check("Review Gate", 41, pr=7)], {"506": TRUSTED_RUN})
        self.assertEqual(rc, 0, err)

    def test_legacy_api_run_alone_exits_0(self):
        rc, err = self.wrapper([api_check("Review Gate", 41)], {})
        self.assertEqual(rc, 0, err)

    def test_trusted_pair_job_of_another_pr_exits_1(self):
        # A closed-unmerged child's run on this head: no PR listing shows it, its run title does.
        for title in ("Review Gate - PR #8", "Review Gate - PR #77", "Review Gate - PR", "Review Gate"):
            with self.subTest(title=title):
                rc, err = self.wrapper([job("Review Gate", 517)], {"517": TRUSTED_RUN},
                                       fixture={"titles": {"517": title}})
                self.assertEqual(rc, 1, err)
                self.assertIn("not 'Review Gate - PR #7'", err)

    def test_untrusted_jobs_exit_1(self):
        for pair in (".github/workflows/forge.yml\tpull_request",
                     ".github/workflows/forge.yml\tpull_request_target",
                     f"{RG_PATH}\tpull_request"):  # a PR-edited review-gate.yml runs under pull_request
            with self.subTest(pair=pair):
                rc, err = self.wrapper([job("Review Gate", 508)], {"508": pair})
                self.assertEqual(rc, 1, err)
                self.assertIn("untrusted workflow", err)

    def test_untrusted_job_is_forged_even_beside_a_trusted_one(self):
        rc, err = self.wrapper([job("Review Gate", 506), job("Review Gate", 508)],
                               {"506": TRUSTED_RUN, "508": ".github/workflows/forge.yml\tpull_request"})
        self.assertEqual(rc, 1, err)
        self.assertIn("runs/508", err)
        self.assertNotIn("runs/506", err)

    def test_ambiguous_input_exits_2(self):
        for kwargs in ({"PR_NUMBER": None}, {"PR_NUMBER": "7abc"}, {"fixture": {"titles": {}}}):
            with self.subTest(kwargs=str(kwargs)):
                rc, err = self.wrapper([job("Review Gate", 514)], {"514": TRUSTED_RUN}, **kwargs)
                self.assertEqual(rc, 2, err)

    # aec #154 (dba592db): empty or runless input cannot be evaluated, so it fails closed.
    def test_empty_listing_exits_2(self):
        for stdin in ("", json.dumps({"total_count": 0, "check_runs": []})):
            with self.subTest(stdin=stdin):
                rc, err = self.wrapper([], {}, stdin=stdin)
                self.assertEqual(rc, 2, err)


class CopMergeCommand(unittest.TestCase):
    def test_documented_command_never_runs_the_pr_checkout(self):
        # A PR controls its checkout's scripts/, so the cop's merge-time run must use the installed skill.
        doc_path = SKILL.parent / "pr-merge-flow" / "SKILL.md"
        if not doc_path.exists():
            self.skipTest("pr-merge-flow is not installed beside review-gate (vendored layout)")
        doc = doc_path.read_text()
        runs = [l for l in doc.splitlines() if "python3" in l and "check-forged-review-gate.py" in l]
        self.assertTrue(runs)
        for line in runs:
            self.assertIn("python3 ~/.claude/skills/review-gate/scripts/check-forged-review-gate.py", line)
            self.assertNotRegex(line, r"python3 (\./)?scripts/")


class InstalledCopies(unittest.TestCase):
    def test_repo_copies_match_skill_copies(self):
        # This repo's own gate loads scripts/ and .github/workflows/ from main; keep them the skill's copies.
        # The repo that installed the gate: SKILL.parent here; the repo root when vendored under .claude/skills.
        root = next((d for d in SKILL.parents if (d / ".github/workflows/review-gate.yml").is_file()), None)
        if root is None:
            self.skipTest("review-gate is not installed into a repo above this skill")
        for name in ("check-forged-gate-names.py", "check-forged-review-gate.py", "check-review-gate.py"):
            self.assertEqual((root / "scripts" / name).read_bytes(), (SCRIPTS / name).read_bytes(), name)
        self.assertEqual((root / ".github/workflows/review-gate.yml").read_bytes(), TEMPLATE.read_bytes())


if __name__ == "__main__":
    unittest.main()
