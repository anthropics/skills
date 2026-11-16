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
import json, tempfile
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

def _gh(rc=0, rollup=None, err=""):
    return lambda *a, **k: _R(rc, json.dumps({"statusCheckRollup": rollup}), err)

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
def run(name, concl, at, wf="Review Gate"):
    return {"name": name, "workflowName": wf, "conclusion": concl, "startedAt": at}
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
# an older run still in progress does not outrank a newer green run
assert merge("gh pr merge 5 --squash --match-head-commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", rollup=ok + [{"name": "Review Gate", "workflowName": "Review Gate", "conclusion": "", "startedAt": "2026-11-15T10:00:00Z"}, latest_ok]) is None
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
