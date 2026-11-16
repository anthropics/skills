"""Run: python3 pr-merge-flow/tests/test_pr_guard.py  (no framework; exits non-zero on failure)."""
import importlib.util
from pathlib import Path

spec = importlib.util.spec_from_file_location("g", Path(__file__).parent.parent / "scripts" / "pr-guard.py")
g = importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)

calls = lambda c: list(g.sync_calls(c, "/r"))

# What agents actually ran on 2026-09-28 (email_demo #516/#518 rebuilt twice for nothing).
assert calls('for w in a b; do git -C .worktrees/$w merge -q --no-edit origin/staging; done') == \
    [(".worktrees/$w", "merge", ["origin/staging"])]
assert calls("cd /x/wt && git fetch -q origin staging && git merge origin/staging --no-edit") == \
    [("/x/wt", "merge", ["origin/staging"])]
assert calls("git pull --rebase origin staging") == [("/r", "pull", ["origin", "staging"])]
assert calls('git merge -m "sync staging" origin/staging') == [("/r", "merge", ["origin/staging"])]
assert calls("git -C sub rebase origin/main") == [("/r/sub", "rebase", ["origin/main"])]
# Not syncs: no ref named, control flags, other git commands.
assert calls("git pull") == []
assert calls("git merge --abort") == []
assert calls("git rebase --continue") == []
assert calls("git log origin/staging..HEAD") == []
assert calls("gh pr merge 5 --merge") == []

assert g.names_base(["origin", "staging"], "staging")
assert g.names_base(["origin/staging"], "staging")
assert not g.names_base(["origin/feat/x"], "staging")

# Unresolvable dir is refused before any network call; override lets it through.
assert "can't resolve" in g.check("for w in a; do git -C wt/$w merge origin/staging; done", "/r")
assert g.check("git -C wt/$w merge origin/staging  # sync-base: need fix abc123", "/r") is None

assert g.draft_violation("gh pr create --draft --title x")
assert g.draft_violation("git push && gh pr create -d")
assert g.draft_violation("gh pr ready 5 --undo")
assert not g.draft_violation("gh pr create --title 'no draft here'")
assert list(g.pr_create_dirs("git push && gh pr create --title x", "/r"))
assert not list(g.pr_create_dirs("gh pr create -R me/r --title x", "/r"))
assert not list(g.pr_create_dirs("gh pr create --repo=me/r", "/r"))
# Codex P2s on #37: quoting, continuation, other ref spellings, gh aliases/inherited -R.
assert calls('git merge -m "sync; base" origin/main') == [("/r", "merge", ["origin/main"])]
assert calls("git merge \\\n  origin/staging") == [("/r", "merge", ["origin/staging"])]
assert calls("git merge origin/staging # sync; not a command") == [("/r", "merge", ["origin/staging"])]
assert calls('git commit -m "" && git merge origin/staging') == [("/r", "merge", ["origin/staging"])]
assert calls("if true; then git -C wt rebase origin/main; fi") == [("/r/wt", "rebase", ["origin/main"])]
for ref in ["refs/heads/main", "refs/remotes/upstream/main", "company/main", "refs/remotes/origin/main"]:
    assert g.names_base([ref], "main"), ref
assert not g.names_base(["refs/heads/feat/main-fix", "a/b/main"], "main")
assert g.draft_violation("gh pr create \\\n  --draft --title x")
assert g.draft_violation("gh pr new --draft")
assert g.draft_violation("gh -R owner/repo pr create --draft")
assert not g.draft_violation('gh pr create --title "no --draft; here"')
assert not list(g.pr_create_dirs("gh -R me/r pr create --title x", "/r"))
assert list(g.pr_create_dirs("gh pr new --title x", "/r"))
# Codex on #38: a comment ends at the newline, and `#` inside a word or quotes isn't one.
assert g.draft_violation("echo ok # note\ngh pr create --draft")
assert g.draft_violation("echo x#not-a-comment; gh pr create --draft")
assert g.draft_violation('gh pr create --title "#12 fix" --draft')
assert g.draft_violation("gh pr create --title '# heading' --draft")
assert not g.draft_violation("gh pr create --title x  # later: --draft")
assert calls("git status # merge origin/main later\ngit merge origin/staging") == \
    [("/r", "merge", ["origin/staging"])]
# Heredoc bodies are data, not commands, and must not hide what follows.
assert g.draft_violation("cat <<'EOF'\n\"\nEOF\ngh pr create --draft")
assert g.draft_violation("cat <<-EOF > f\n\tit's\n\tEOF\ngh pr create --draft")
assert not g.draft_violation("cat <<EOF\ngh pr create --draft\nEOF")
# Codex round 2 on #38: slashed base names, quoted heredoc delimiters, attached -R.
for ref in ["release/v1", "origin/release/v1", "refs/remotes/origin/release/v1", "refs/heads/release/v1"]:
    assert g.names_base([ref], "release/v1"), ref
assert not g.names_base(["a/b/release/v1", "origin/release/v10"], "release/v1")
assert g.draft_violation("cat <<E\\OF\nx\nEOF\ngh pr create --draft")
assert g.draft_violation("cat <<'E'OF\nx\nEOF\ngh pr create --draft")
assert g.draft_violation('cat <<"EOF"\nx\nEOF\ngh pr create --draft')
# A heredoc whose terminator never appears drops nothing (fails toward checking).
assert g.draft_violation("cat <<EOF\nx\ngh pr create --draft")
assert not list(g.pr_create_dirs("gh -Rme/r pr create --title x", "/r"))
assert not list(g.pr_create_dirs("gh pr create -Rme/r", "/r"))
# Codex round 3 (post-merge on #38): subshell cd scope, fail-closed fallback, $'..' delimiters.
assert calls("(cd /tmp; :); git merge origin/main") == [("/r", "merge", ["origin/main"])]
assert calls("(cd /tmp && git merge origin/main)") == [("/tmp", "merge", ["origin/main"])]
assert calls("cd a && (cd b; git merge origin/x); git merge origin/y") == \
    [("/r/a/b", "merge", ["origin/x"]), ("/r/a", "merge", ["origin/y"])]
assert g.draft_violation("printf $'\\''; gh pr create --draft")
assert g.draft_violation("cat <<$'EOF'\nx\nEOF\ngh pr create --draft\n$EOF")
# Quoted or escaped operator characters are arguments, not shell syntax.
assert calls("printf '('; cd /tmp/repo; printf ')'; git merge origin/main") == \
    [("/tmp/repo", "merge", ["origin/main"])]
assert calls("echo \\( ; cd /x; echo \\) ; git merge origin/main") == [("/x", "merge", ["origin/main"])]
assert g.draft_violation("echo ';' && gh pr create --draft")
assert list(g.segments("echo ';' '|'")) == [["echo", ";", "|"]]
assert g.draft_violation("gh pr create --title '\n' --draft")
assert g.draft_violation('gh pr create --title "a\nb" --draft')
# Unparseable input still keeps line boundaries.
assert g.draft_violation("echo 'unterminated\ngh pr create --draft")

# pr_open_mode: only an explicit "draft" allows drafts; unset, ready and corrupt mean ready.
import json, re, tempfile
_prefs = Path(tempfile.mkdtemp()) / "preferences.json"
assert not g.draft_mode(_prefs)  # missing file
for body, want in [({}, False), ({"settings": {}}, False), ({"settings": {"pr_open_mode": "ready"}}, False),
                   ({"settings": {"pr_open_mode": "draft"}}, True), ({"settings": None}, False)]:
    _prefs.write_text(json.dumps(body))
    assert g.draft_mode(_prefs) is want, body
_prefs.write_text("{not json")
assert not g.draft_mode(_prefs)

# Ungated merge and polling. Mock the gh call the way a green/red rollup would come back.
class _R:
    def __init__(self, rc, out="", err=""):
        self.returncode, self.stdout, self.stderr = rc, out, err

HEAD_SHA = "a" * 40
def _gh(rc=0, rollup=None, err="", paths=None, api_rc=0, events=None, forged=()):
    """`gh pr view` returns the rollup; `gh api .../actions/runs` resolves each run id to its workflow
    file. By default a run's path follows its workflowName; `paths` overrides it per run id (None =
    the API does not list that run), `events` overrides the event. `.../runs/<id>/jobs` lists every
    rollup entry's job as real, except entries in `forged` (custom checks with a borrowed detailsUrl)."""
    def run(args, *a, **k):
        if args[:2] == ["gh", "api"] and "/jobs?" in args[3]:
            run_id = re.search(r"/runs/(\d+)/jobs", args[3]).group(1)
            rows = [(m.group(2), e.get("name"), (e.get("conclusion") or "").upper()) for e in rollup or []
                    if id(e) not in {id(f) for f in forged}
                    and (m := g.RUN_ID.search(e.get("detailsUrl") or "")) and m.group(1) == run_id]
            return _R(api_rc, "".join(f"{j}\t{n}\t{c}\n" for j, n, c in rows), "boom" if api_rc else "")
        if args[:2] == ["gh", "api"]:
            assert f"head_sha={HEAD_SHA}" in args[3], args
            rows = {}
            for e in rollup or []:
                m = g.RUN_ID.search(e.get("detailsUrl") or "")
                if m and e.get("workflowName"):
                    rows[m.group(1)] = f".github/workflows/{e['workflowName'].lower().replace(' ', '-')}.yml"
            rows.update(paths or {})
            return _R(api_rc, "".join(f"{i}\t{pth}\t{(events or {}).get(i, 'pull_request')}\n"
                                      for i, pth in rows.items() if pth), "boom" if api_rc else "")
        return _R(rc, json.dumps({"statusCheckRollup": rollup, "headRefOid": HEAD_SHA}), err)
    return run

_run = g.subprocess.run
def merge(cmd, **kw):
    g.subprocess.run = _gh(**kw)
    try:
        return g.check(cmd, "/r")
    finally:
        g.subprocess.run = _run

ok = [{"name": "pytest", "conclusion": "SUCCESS"}, {"name": "lint", "conclusion": "skipped"},
      {"context": "ci/x", "state": "SUCCESS"}, {"name": "n", "conclusion": "NEUTRAL"}]
assert "--admin" in merge("gh pr merge 5 --admin --squash", rollup=ok)
assert "never bypass" in merge("gh pr merge 5 --admin --auto", rollup=ok)
assert "never `--auto`" in merge("gh pr merge 5 --auto --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok)
assert "pin the reviewed head" in merge("gh pr merge 5 --squash", rollup=ok)
# Codex P1 on #82 (round 7): an unset $SHA expands to an empty value; a short SHA is not a pin either.
assert "pin the reviewed head" in merge('gh pr merge 5 --squash --match-head-commit ""', rollup=ok)
assert "pin the reviewed head" in merge("gh pr merge 5 --squash --match-head-commit=", rollup=ok)
assert "pin the reviewed head" in merge("gh pr merge 5 --squash --match-head-commit abc1234", rollup=ok)
# Codex P2 on #82: --disable-auto merges nothing, so it needs no head pin or green checks.
assert merge("gh pr merge 5 --disable-auto", rollup=[]) is None
assert merge("gh -R o/r pr merge 5 --disable-auto", rollup=[]) is None
assert "never `--auto`" in merge("gh pr merge 5 --disable-auto --auto", rollup=ok)
assert "never bypass" in merge("gh pr merge 5 --disable-auto --admin", rollup=ok)
# Codex P1 on #82 (round 6): `--disable-auto=false` leaves the option off, so it merges: full checks.
assert "pin the reviewed head" in merge("gh pr merge 5 --disable-auto=false --squash", rollup=ok)
assert merge("gh pr merge 5 --disable-auto=true", rollup=[]) is None
assert "pin the reviewed head" in merge("gh pr merge 5 --body --disable-auto --squash", rollup=ok)
# 1.4.3: pflag bool flags are last-wins. `--disable-auto --disable-auto=false` merges: full checks.
assert "pin the reviewed head" in merge("gh pr merge 5 --disable-auto --disable-auto=false --squash", rollup=ok)
assert merge("gh pr merge 5 --disable-auto=false --disable-auto", rollup=[]) is None
assert "never `--auto`" in merge("gh pr merge 5 --auto=false --auto --squash", rollup=ok)
assert "never bypass" in merge("gh pr merge 5 --admin=0 --admin=1 --squash", rollup=ok)
assert merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok) is None
assert merge("gh pr merge 5 --squash --match-head-commit=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok) is None
# Codex P1 on #82: the status lookup must target the -R/--repo repo, not the cwd repo.
def _gh_repo(want):
    def run(args, *a, **k):
        i = args.index("-R") if "-R" in args else -1
        if i < 0 or args[i + 1] != want:  # gh resolved the PR in the cwd repo: the live failure
            return _R(1, "", "Could not resolve to a PullRequest")
        return _R(0, json.dumps({"statusCheckRollup": ok}))
    return run
for c in ["gh -R owner/target pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "gh pr merge 5 -R owner/target --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "gh pr merge 5 --repo owner/target --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "gh --repo=owner/target pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "gh pr merge 5 -Rowner/target --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          # Codex P2 on #82: repeated repo flags, last wins (as gh does), in every spelling.
          "gh -R owner/safe pr merge 5 -R owner/target --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "gh --repo=owner/safe pr merge 5 --repo owner/target --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "gh -Rowner/safe pr merge 5 --repo=owner/target --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "gh --repo owner/safe pr merge 5 -Rowner/target --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          # Codex P2 on #82 (round 6): a value flag consumes the next token, so a repo-looking
          # --body/-t value is text, not a repo, and a value-looking --disable-auto is not a flag.
          "gh -R owner/target pr merge 5 --body --repo=owner/green --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "gh -R owner/target pr merge 5 -t -Rowner/green --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "gh pr merge 5 -R owner/target --body -R --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"]:
    g.subprocess.run = _gh_repo("owner/target")
    try:
        assert g.check(c, "/r") is None, (c, g.check(c, "/r"))
    finally:
        g.subprocess.run = _run
# Codex P1 on #82 (round 3 of repo parsing): clustered short flags carrying R fail closed.
for c in ["gh pr merge 5 -dR owner/target --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "gh pr merge 5 -dRowner/target --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "gh pr merge 5 -Rd --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa -R"]:
    g.subprocess.run = _gh_repo("owner/target")
    try:
        assert "standalone `-R owner/repo`" in (g.check(c, "/r") or ""), c
    finally:
        g.subprocess.run = _run
g.subprocess.run = _gh_repo("owner/target")
try:
    assert "Could not resolve" in g.check("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "/r")
finally:
    g.subprocess.run = _run
# prevost#379 P2: `--admin=false` / `--auto=false` turn the option off, so the call takes the normal checks.
assert merge("gh pr merge 5 --admin=false --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok) is None
assert merge("gh pr merge 5 --auto=false --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok) is None
assert "never bypass" in merge("gh pr merge 5 --admin=true --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok)
# prevost#379 P1: any short-flag cluster fails closed (`-st 5 6`: gh merges 6 with title 5).
for c in ["gh pr merge -st 5 6 --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "gh pr merge 6 -sd --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"]:
    assert "can't parse this merge" in merge(c, rollup=ok), c
# prevost#379 P1: the status lookup runs in the merge's effective dir (`cd`, `env -C`), not the hook's cwd.
def _gh_cwd(want):
    def run(args, *a, cwd=None, **k):
        rollup = ok if cwd == want else [{"name": "pytest", "conclusion": "FAILURE"}]
        return _R(0, json.dumps({"statusCheckRollup": rollup}))
    return run
for c, want in [("cd /other && gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "/other"),
                ("env -C /other gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "/other"),
                ("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "/r")]:
    g.subprocess.run = _gh_cwd(want)
    try:
        assert g.check(c, "/r") is None, (c, g.check(c, "/r"))
        g.subprocess.run = _gh_cwd("/r" if want != "/r" else "/x")
        assert "not all green" in (g.check(c, "/r") or ""), c
    finally:
        g.subprocess.run = _run
assert "working directory" in merge("cd $D && gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok)
# claude-skills#83 Codex: a cd in a background job / pipeline stage doesn't reach the merge: fail closed.
for c in ["cd /other & gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "cd /other | gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "cd /other |& gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
          "cd /other &>/dev/null & gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"]:
    assert "working directory" in (merge(c, rollup=ok) or ""), c
assert merge("cd /other && gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 2>&1", rollup=ok) is None
# Redirections and quoted operators are not pipeline boundaries.
for c in ["cd /other && gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa &>/dev/null",
          "cd /other && gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa >&2",
          "cd /other && gh pr merge 5 -b 'a | b & c' --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"]:
    assert merge(c, rollup=ok) is None, (c, merge(c, rollup=ok))
# Backtick dirs are as unresolved as $(…); an explicit -R makes the dir irrelevant.
assert "working directory" in merge("cd `pwd`/x && gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok)
g.subprocess.run = _gh_repo("owner/target")
try:
    for c in ['cd "$D" && gh pr merge 5 -R owner/target --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
              "cd `x` && gh pr merge 5 -R owner/target --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"]:
        assert g.check(c, "/r") is None, (c, g.check(c, "/r"))
finally:
    g.subprocess.run = _run
assert merge("gh pr merge https://github.com/o/r/pull/5 -t 'x y' --merge --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok) is None
for bad, name in [({"name": "pytest", "conclusion": "CANCELLED"}, "pytest: CANCELLED"),
                  ({"name": "pytest", "conclusion": ""}, "pytest: PENDING"),
                  ({"name": "pytest", "conclusion": "FAILURE"}, "pytest: FAILURE"),
                  ({"context": "ci/x", "state": "PENDING"}, "ci/x: PENDING"),
                  ({"context": "ci/x", "state": "FAILURE"}, "ci/x: FAILURE")]:
    m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [bad])
    assert m and name in m and "--watch --fail-fast" in m, (bad, m)
# Only the LATEST run per check name counts: a historical red Review Gate run must not block
# once a newer run of the same check is green (every new PR leaves one, nevar-design#7).
_run_ids = iter(range(1000, 10**6))
def run(name, concl, at, wf="Review Gate"):  # each call is its own workflow run, as gh reports it
    return {"name": name, "workflowName": wf, "conclusion": concl, "startedAt": at,
            "detailsUrl": f"https://github.com/o/r/actions/runs/{next(_run_ids)}/job/1"}
old_red = [run("Review Gate", "FAILURE", "2026-11-15T10:00:00Z"), run("Review Gate", "CANCELLED", "2026-11-15T10:05:00Z")]
latest_ok = run("Review Gate", "SUCCESS", "2026-11-15T10:10:00Z")
assert merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + old_red + [latest_ok]) is None
assert merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [latest_ok] + old_red) is None  # order-independent
m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [run("Review Gate", "SUCCESS", "2026-11-15T10:00:00Z"),
                                                   run("Review Gate", "FAILURE", "2026-11-15T10:10:00Z")])
assert m and "Review Gate: FAILURE" in m, m  # newest red still blocks
m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [run("Review Gate", "SUCCESS", "2026-11-15T10:00:00Z"),
                                                   run("Review Gate", "", "2026-11-15T10:10:00Z")])
assert m and "Review Gate: PENDING" in m, m  # a re-run in flight blocks
m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + old_red + [latest_ok, run("pytest", "FAILURE", "2026-11-15T10:00:00Z", "CI")])
assert m and "pytest: FAILURE" in m and "Review Gate" not in m, m  # other checks stay independent
# a queued rerun has no startedAt: it still beats the older green run and blocks
m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [latest_ok, {"name": "Review Gate", "workflowName": "Review Gate", "conclusion": "", "status": "QUEUED", "startedAt": None}])
assert m and "Review Gate: PENDING" in m, m
# 1.4.3: same-second reruns: a SUCCESS must not hide a FAILURE, in either list order
for pair in ([run("Review Gate", "FAILURE", "2026-11-15T10:10:00Z"), latest_ok],
             [latest_ok, run("Review Gate", "FAILURE", "2026-11-15T10:10:00Z")]):
    m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + pair)
    assert m and "Review Gate: FAILURE" in m, (pair, m)
# ...and ids do not order them either: same-run sibling jobs (higher job id) and different runs alike
def job_run(concl, run_id, job_id):
    return dict(run("Review Gate", concl, "2026-11-15T10:10:00Z"),
                detailsUrl=f"https://github.com/o/r/actions/runs/{run_id}/job/{job_id}")
for pair in ([job_run("FAILURE", 100, 1), job_run("SUCCESS", 100, 2)], [job_run("SUCCESS", 100, 2), job_run("FAILURE", 100, 1)],
             [job_run("FAILURE", 100, 1), job_run("SUCCESS", 101, 2)], [job_run("SUCCESS", 101, 2), job_run("FAILURE", 100, 1)]):
    m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + pair)
    assert m and "Review Gate: FAILURE" in m, (pair, m)
# 1.4.5 (nevar-fund #25 Codex P1): identity is the run id, not the name. A distinct same-named job
# in the SAME run (e.g. one with `needs:`) that starts later and is green must not hide a failed one.
def at_job(concl, run_id, job_id, at):
    return dict(run("Review Gate", concl, at), detailsUrl=f"https://github.com/o/r/actions/runs/{run_id}/job/{job_id}")
for pair in ([at_job("FAILURE", 100, 1, "2026-11-15T10:00:00Z"), at_job("SUCCESS", 100, 2, "2026-11-15T10:10:00Z")],
             [at_job("SUCCESS", 100, 2, "2026-11-15T10:10:00Z"), at_job("FAILURE", 100, 1, "2026-11-15T10:00:00Z")]):
    m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + pair)
    assert m and "Review Gate: FAILURE" in m, (pair, m)
# ...while a newer run of the workflow (a true rerun) still supersedes the older run's failure,
assert merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [
    at_job("FAILURE", 100, 1, "2026-11-15T10:00:00Z"), at_job("SUCCESS", 101, 5, "2026-11-15T10:10:00Z")]) is None
# even when the old run's own later sibling job started after the new run did,
assert merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [
    at_job("FAILURE", 100, 1, "2026-11-15T10:00:00Z"), at_job("SUCCESS", 100, 2, "2026-11-15T10:20:00Z"),
    at_job("SUCCESS", 101, 5, "2026-11-15T10:10:00Z")]) is None
# and every same-named job of that newest run must be green.
m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [
    at_job("SUCCESS", 100, 1, "2026-11-15T10:00:00Z"), at_job("SUCCESS", 101, 5, "2026-11-15T10:10:00Z"),
    at_job("FAILURE", 101, 6, "2026-11-15T10:15:00Z")])
assert m and "Review Gate: FAILURE" in m, m
# #88 Codex P1 (r4582093085): a run's start spans ALL its jobs. Run 100 starts 10:00 (build) and its
# dependency-delayed `gate` goes green at 10:20; run 101 starts 10:10 and its `gate` fails at 10:15.
def wf_job(name, concl, run_id, job_id, at):
    return {"name": name, "workflowName": "CI", "conclusion": concl, "startedAt": at,
            "detailsUrl": f"https://github.com/o/r/actions/runs/{run_id}/job/{job_id}"}
m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [
    wf_job("build", "SUCCESS", 100, 1, "2026-11-15T10:00:00Z"), wf_job("gate", "SUCCESS", 100, 2, "2026-11-15T10:20:00Z"),
    wf_job("build", "SUCCESS", 101, 3, "2026-11-15T10:10:00Z"), wf_job("gate", "FAILURE", 101, 4, "2026-11-15T10:15:00Z")])
assert m and "gate: FAILURE" in m, m
# #88 Codex P1 (r4582226134): without a parsable run id the run identity is unknown, so a later
# green job must not supersede an earlier failed one (missing or unrecognized detailsUrl alike).
for url in (None, "https://example.com/not-a-job"):
    m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [
        {"name": "Review Gate", "workflowName": "Review Gate", "conclusion": "FAILURE", "startedAt": "2026-11-15T10:00:00Z", "detailsUrl": url},
        {"name": "Review Gate", "workflowName": "Review Gate", "conclusion": "SUCCESS", "startedAt": "2026-11-15T10:10:00Z", "detailsUrl": url}])
    assert m and "Review Gate: FAILURE" in m, (url, m)
# 1.4.6 (nevar-integrations#11 Codex P1 r4582423865): workflow identity is the run's file path, not
# its editable `name:`. A PR-added workflow also named `CI` with a later green `Foundation checks` job
# must not supersede the real CI run's failed `Foundation checks`.
real = wf_job("Foundation checks", "FAILURE", 200, 1, "2026-11-15T10:00:00Z")
fake = wf_job("Foundation checks", "SUCCESS", 201, 2, "2026-11-15T10:10:00Z")
for paths in ({"200": ".github/workflows/ci.yml", "201": ".github/workflows/sneaky.yml"},  # two paths, one name
              {"201": None},  # the API does not list the newer run: unresolved, supersedes nothing
              {"200": ".github/workflows/ci.yml", "201": ".github/workflows/ci.yml", "x": "y"}):
    pr_merge = "gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    g.subprocess.run = _gh(rollup=ok + [real, fake], paths=paths)
    try:
        m = g.check(pr_merge, "/r")
    finally:
        g.subprocess.run = _run
    if paths["201"] == ".github/workflows/ci.yml":
        assert m is None, (paths, m)  # a true rerun of the same workflow file still supersedes
    else:
        assert m and "Foundation checks: FAILURE" in m, (paths, m)
# One workflow file, two events: a newer green pull_request run never supersedes an older red
# pull_request_target run of the same file (identity is (path, event, job name)).
for events, blocked in (({"200": "pull_request_target", "201": "pull_request"}, True),
                        ({"200": "pull_request", "201": "pull_request"}, False)):
    g.subprocess.run = _gh(rollup=ok + [real, fake], paths={"200": ".github/workflows/ci.yml", "201": ".github/workflows/ci.yml"},
                           events=events)
    try:
        m = g.check("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "/r")
    finally:
        g.subprocess.run = _run
    assert bool(m) is blocked and (not blocked or "Foundation checks: FAILURE" in m), (events, m)
# #90 Codex P1 (r4582487271): a custom green check whose writable detailsUrl names a job in a newer
# legitimate run of the same workflow file is not that run's job, so it supersedes nothing.
newer_build = wf_job("build", "SUCCESS", 202, 7, "2026-11-15T10:10:00Z")
custom = wf_job("Foundation checks", "SUCCESS", 202, 7, "2026-11-15T10:11:00Z")  # borrows job 7's URL
for bad in (dict(custom), dict(custom, detailsUrl="https://github.com/o/r/actions/runs/202/job/99")):
    g.subprocess.run = _gh(rollup=ok + [real, newer_build, bad], forged=(bad,))
    try:
        m = g.check("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "/r")
    finally:
        g.subprocess.run = _run
    assert m and "Foundation checks: FAILURE" in m, (bad, m)
# the Actions API failing resolves nothing, so nothing is superseded (fail closed)
m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + old_red + [latest_ok], api_rc=1)
assert m and "Review Gate: FAILURE" in m, m
# #90 Codex P2 (r4582534724): every gh call shares one deadline under the hook's 20 s timeout. Each
# call here "takes" 6 s, so the newer run's jobs lookup is past the 15 s budget: it is skipped, that
# run supersedes nothing (fail closed), and no call is ever given a timeout past the deadline.
_clock, _timeouts, _gh_slow = [0.0], [], _gh(rollup=ok + [real, fake], paths={"200": ".github/workflows/ci.yml", "201": ".github/workflows/ci.yml"})
def _slow(args, *a, **k):
    _timeouts.append((_clock[0], k["timeout"]))
    _clock[0] += 6
    return _gh_slow(args, *a, **k)
g.subprocess.run, _mono, g.time.monotonic = _slow, g.time.monotonic, lambda: _clock[0]
try:
    m = g.check("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "/r")
finally:
    g.subprocess.run, g.time.monotonic = _run, _mono
assert m and "Foundation checks: FAILURE" in m, m
assert len(_timeouts) == 3 and all(t0 + t <= g.GH_BUDGET_S for t0, t in _timeouts), _timeouts
# an older run still in progress does not outrank a newer green run
assert merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [run("Review Gate", "", "2026-11-15T10:00:00Z"), latest_ok]) is None
# an undated completed rerun cannot be ordered, so it fails closed
m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [latest_ok, {"name": "Review Gate", "workflowName": "Review Gate", "conclusion": "CANCELLED", "startedAt": None}])
assert m and "Review Gate: CANCELLED" in m, m
# gh emits the zero time, not null, for a missing startedAt
m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [latest_ok, {"name": "Review Gate", "workflowName": "Review Gate", "conclusion": "CANCELLED", "startedAt": "0001-01-01T00:00:00Z"}])
assert m and "Review Gate: CANCELLED" in m, m
# same-named third-party check runs from different apps are never collapsed
m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [{"__typename": "CheckRun", "name": "scan", "conclusion": "FAILURE", "startedAt": "2026-11-15T10:00:00Z"},
                                                   {"__typename": "CheckRun", "name": "scan", "conclusion": "SUCCESS", "startedAt": "2026-11-15T10:05:00Z"}])
assert m and "scan: FAILURE" in m, m
# a check run and a same-named status context are separate requirements
m = merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [{"__typename": "CheckRun", "name": "deploy", "conclusion": "FAILURE", "startedAt": "2026-11-15T10:00:00Z"},
                                                   {"__typename": "StatusContext", "context": "deploy", "state": "SUCCESS"}])
assert m and "deploy: FAILURE" in m, m
assert "no checks" in merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=[])
assert "no checks" in merge("gh pr merge 5 --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=None)
m = merge("gh pr merge 5 --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rc=1, err="no pull requests found")
assert m and "no pull requests found" in m
assert merge("gh pr view 5 && echo done", rollup=[]) is None

for c in ["while true; do gh pr checks 12 | grep -q pending || break; sleep 30; done",
          "sleep 60 && gh pr view 12", "gh run watch 9; sleep 1", "until gh run list; do sleep 5; done",
          "for i in 1 2; do sleep 10\n gh pr status\n done"]:
    assert "never poll" in (g.check(c, "/r") or ""), c
for c in ["gh pr checks 12 --watch --fail-fast", "sleep 5", "gh pr view 12", "echo gh pr checks; sleep 5",
          "sleep 5 # gh pr checks 12", "cat <<EOF\ngh pr checks 12\nEOF\nsleep 5"]:
    assert g.check(c, "/r") is None, c
print("ok")

# Codex on prevost #332: the fork check uses the dir `gh pr create` runs in, not the hook cwd.
seen = []
g.unpinned_fork = lambda d: seen.append(d)
def forks(c):
    seen.clear()
    assert g.check(c, "/hook") is None
    return list(seen)
assert forks("cd /some/fork && gh pr create --title x") == ["/some/fork"]
assert forks("(cd /some/fork && gh pr create --title x) && gh pr create -R o/r --title y") == ["/some/fork"]
assert forks("gh pr create --title x") == ["/hook"]
assert forks('cd "$DIR" && gh pr create --title x') == []
# Codex P2 on prevost #332: `env` and NAME=value prefixes don't hide the command.
assert calls("GIT_DIR=x env -i FOO=1 git merge origin/main") == [("/r", "merge", ["origin/main"])]
assert calls("env -u HOME git -C wt rebase origin/main") == [("/r/wt", "rebase", ["origin/main"])]
assert g.draft_violation("GH_TOKEN=x env gh pr create --draft")
assert "--admin" in merge("GH_TOKEN=x gh pr merge 5 --admin", rollup=ok)
assert calls("echo a=b; git merge origin/main") == [("/r", "merge", ["origin/main"])]  # only a leading assignment
# Codex P2 on prevost #332: cd options and `--` come before the directory operand.
assert calls("cd -P wt && git merge origin/main") == [("/r/wt", "merge", ["origin/main"])]
assert calls("cd -- wt && git merge origin/main") == [("/r/wt", "merge", ["origin/main"])]
# Codex P2s on prevost #332, round 5: directory changes the guard can't model fail closed instead of being ignored.
assert calls("cd - && git merge origin/main") == [("$OLDPWD", "merge", ["origin/main"])]
assert calls("cd && git merge origin/main") == [("$HOME", "merge", ["origin/main"])]
assert calls("pushd wt && git merge origin/main") == [("$DIRSTACK", "merge", ["origin/main"])]
# `env -C DIR cmd` runs that one command in DIR; the next command is back in the original directory.
assert calls("env -C wt git merge origin/main; git merge origin/main") == [("/r/wt", "merge", ["origin/main"]), ("/r", "merge", ["origin/main"])]
assert calls("env --chdir=wt git merge origin/main") == [("/r/wt", "merge", ["origin/main"])]
assert g.draft_violation("env -C wt gh pr create --draft")
# Codex P2s on prevost #332, round 6: pflag bool values on the draft flags, and the override is a comment, not a substring.
assert g.draft_violation("gh pr create --draft=true") and g.draft_violation("gh pr create -d=1")
assert g.draft_violation("gh pr ready 5 --undo=true")
assert not g.draft_violation("gh pr create --draft=false") and not g.draft_violation("gh pr ready 5 --undo=false")
assert g.check("git commit -m 'document sync-base: behavior' && git -C wt/$w merge origin/staging", "/r") is not None
assert g.check("git -C wt/$w merge origin/staging # sync-base: need abc123", "/r") is None

# nevar-fund #24 Codex P1: the `command` builtin runs its operand, so `command [-p] [--] gh …` is `gh …`.
for pre in ("command ", "command -p ", "command -- ", "command -p -- "):
    assert "--admin" in merge(pre + "gh pr merge 5 --admin --squash", rollup=ok), pre
    assert g.draft_violation(pre + "gh pr create --draft"), pre
    assert calls(pre + "git merge origin/main") == [("/r", "merge", ["origin/main"])], pre
# `command -v`/`-V` only look the name up; nothing runs.
assert calls("command -v git merge origin/main") == []
assert not g.draft_violation("command -V gh pr create --draft")


def test_pr_guard():
    """pytest entry point: the asserts above run at import, so a failure is a collection error."""
