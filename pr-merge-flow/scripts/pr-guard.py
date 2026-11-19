#!/usr/bin/env python3
"""PreToolUse guard for PR discipline. Exit 2 blocks the tool call; the stderr
text is what the agent sees.

1. No base sync into a mergeable PR. `git merge|pull|rebase <base>` on a branch
   whose open PR GitHub already reports as mergeable restarts CI and review for
   nothing. Allowed when the PR is DIRTY (a real conflict) or BEHIND (the base
   requires up-to-date branches), and whenever there is no open PR or GitHub
   can't be asked. Override when a specific base commit is genuinely needed:
   add a `# sync-base: <reason>` comment to the command.
2. PRs open ready for review, never as drafts (`gh pr create --draft`,
   `gh pr ready --undo`), unless aec's `pr_open_mode` setting is `draft`
   (`~/.agents-environment-config/preferences.json`). Unset, unreadable or any
   other value means ready.
3. In a fork with no `gh repo set-default`, `gh pr create` without `-R/--repo`
   targets the UPSTREAM repo (a claude-skills PR landed on anthropics/skills
   this way, 2026-09-28). Blocked until the target is explicit.

4. No ungated merge. `gh pr merge --admin` and `--auto` are always blocked (Review Gate does not
   re-run on late review/thread events, so auto-merge can land a PR a late P2 should have
   stopped). Every merge pins the reviewed head with `--match-head-commit <sha>` and needs every
   check SUCCESS/SKIPPED/NEUTRAL (PR #325 merged on a CANCELLED check). Fails closed.
5. No polling: `sleep` plus a `gh pr checks|view|status` / `gh run view|watch|list` query in
   one command. Use `gh pr checks <n> --watch --fail-fast` in the background instead.
6. No Codex mention in a posted comment (`gh pr comment`, `gh issue comment`, `gh pr review`,
   `gh api` fields or `--input`): it spends Matt's Codex quota. Later heads get a fallback review and attestation.
   Override only on Matt's explicit ask: a `# codex-review-ok: <reason>` comment.

Every tool call passes through here, so non-Bash input exits at once.
"""
import json
import os
import re
import shlex
import subprocess
import sys
import time
from pathlib import Path

SYNC_SUBCOMMANDS = {"merge", "pull", "rebase"}
# Anything else, including UNKNOWN, fails open.
MERGEABLE = {"CLEAN", "UNSTABLE", "BLOCKED", "HAS_HOOKS"}
CONTROL_FLAGS = {"--abort", "--continue", "--skip", "--quit", "--edit-todo"}
FLAGS_WITH_VALUE = {"-m", "-F", "-X", "-s", "--message", "--file", "--strategy",
                    "--strategy-option", "--exec", "-x", "--cleanup"}


KEYWORDS = {"do", "then", "else", "elif", "if", "while", "until", "!", "{", "}"}
OPERATORS = set(";&|\n()")
ASSIGN = re.compile(r"[A-Za-z_]\w*=")  # NAME=value prefix
# Quoted/escaped operator chars are swapped for private-use stand-ins before shlex,
# which drops quoting, so `printf '('` stays an argument; swapped back after.
HIDE = {ord(c): 0xE000 + k for k, c in enumerate(";&|()\n")}
UNHIDE = {v: k for k, v in HIDE.items()}


def strip_comments_and_heredocs(cmd, comments=None):
    """Drop `#` comments and heredoc bodies, keeping the newlines that end them.

    shlex gets both wrong: its comments swallow the newline (and start mid-word),
    and it parses heredoc bodies as shell, so one stray quote hides every later
    command. Bash rules: `#` starts a comment only at the start of an unquoted word.
    Dropped comments are appended to `comments` when given (see shell_comments).

    ponytail: `$(...)`/backtick nesting isn't tracked; a `#` or `<<` inside one is
    treated as top-level. Worst case is a missed or extra block, never a crash.
    """
    out, i, n, quote, pending = [], 0, len(cmd), None, []
    while i < n:
        c = cmd[i]
        if quote:
            out.append(c.translate(HIDE))
            if c == "\\" and quote == '"' and i + 1 < n:
                out.append(cmd[i + 1])
                i += 1
            elif c == quote:
                quote = None
            i += 1
        elif c == "\\" and i + 1 < n:
            out.append("\\" + cmd[i + 1].translate(HIDE))
            i += 2
        elif cmd.startswith("$'", i):
            # ANSI-C quoting, where \' doesn't end the string; shlex has no such mode,
            # so re-emit it double-quoted. ponytail: escapes like \n become the letter.
            m = re.match(r"\$'((?:\\.|[^'\\])*)'", cmd[i:], re.S)
            if not m:
                out.append(c)
                i += 1
                continue
            body = re.sub(r"\\(.)", r"\1", m.group(1), flags=re.S)
            out.append('"' + body.replace("\\", "\\\\").replace('"', '\\"').translate(HIDE) + '"')
            i += m.end()
        elif c in "'\"":
            quote = c
            out.append(c)
            i += 1
        elif c == "#" and (not out or out[-1][-1] in " \t\r\n;&|()"):
            start = i
            while i < n and cmd[i] != "\n":
                i += 1
            if comments is not None:
                comments.append(cmd[start:i])
        elif cmd.startswith("<<", i) and not cmd.startswith("<<<", i):
            m = re.match(r"""<<(-?)[ \t]*((?:\\.|'[^']*'|"[^"]*"|[^\s;&|()<>'"\\])+)""", cmd[i:])
            if m:
                try:  # the delimiter is the word after quote removal: <<'E'OF and <<E\OF end at EOF
                    delim = "".join(shlex.split(re.sub(r"\$(?=['\"])", "", m.group(2))))
                except ValueError:
                    delim = m.group(2)
                pending.append((delim, bool(m.group(1))))
                out.append(m.group(0))
                i += m.end()
            else:
                out.append(c)
                i += 1
        elif c == "\n" and pending:
            out.append(c)
            lines, j = cmd[i + 1:].split("\n"), i + 1
            for delim, dash in pending:
                for k, line in enumerate(lines):
                    if (line.lstrip("\t") if dash else line) == delim:
                        j += sum(len(x) + 1 for x in lines[:k + 1])
                        lines = lines[k + 1:]
                        break
                else:  # no terminator: keep the rest, so nothing after it goes unchecked
                    break
            pending = []
            i = min(j, n)
        else:
            out.append(c)
            i += 1
    # An unclosed quote hid everything after it; un-hide so the fallback checks it all.
    return "".join(out).translate(UNHIDE) if quote else "".join(out)


def shell_comments(cmd):
    """The command's real shell comments: not quoted text, not heredoc bodies."""
    comments = []
    strip_comments_and_heredocs(cmd.replace("\\\n", " "), comments)
    return comments


def has_override(cmd, marker):
    """True when a real shell comment carries `# <marker>: <reason>`; the marker inside a quoted
    body or a heredoc is text the command sends, not an override."""
    return any(re.match(rf"#\s*{marker}(?::\s*|\s+)\S", c) for c in shell_comments(cmd))


def shell_tokens(cmd):
    """Shell words and control-operator runs (`&&`, `|&`, `;`, …) in order, or None when shlex can't parse it."""
    lex = shlex.shlex(cmd, posix=True, punctuation_chars=";&|\n()")
    lex.whitespace = " \t\r"
    lex.whitespace_split = True
    lex.commenters = ""
    try:
        return list(lex)
    except ValueError:
        return None


def runs_async(cmd):
    """True when a command joins segments with `&`, `|` or `|&` (a background job or pipeline stage).

    Uses the same tokens as segments(), so quoted text never counts, and `>&`/`&>` redirections
    (`2>&1`, `&>log`) are not operators. Unparseable input counts as async, so callers fail closed.
    """
    toks = shell_tokens(strip_comments_and_heredocs(cmd.replace("\\\n", " ")))
    if toks is None:
        return True
    for i, t in enumerate(toks):
        redirect = t == "&" and ((i and toks[i - 1].endswith(">")) or toks[i + 1:i + 2] and toks[i + 1].startswith(">"))
        if t in ("|", "|&") or (t == "&" and not redirect):
            return True
    return False


def segments(cmd):
    """Split a shell command into argv lists, one per simple command.

    Tokenizes first, so operators inside quotes stay in their argument and
    backslash-newline continues the command, as in Bash.
    """
    cmd = strip_comments_and_heredocs(cmd.replace("\\\n", " "))
    tokens = shell_tokens(cmd)
    if tokens is None:
        # shlex can't parse it (unbalanced or $'..' quotes): split on every operator
        # character, quoted or not. Over-splitting only means more gets checked.
        tokens = [t for part in re.split(r"([;&|()\n])", cmd)
                  for t in ([part] if part in OPERATORS else part.split())]
    argv = []
    for t in tokens + [";"]:
        if t and set(t) <= OPERATORS:
            # Keywords and NAME=value prefixes don't change the command; neither does `env [-i] [-u NAME] [NAME=value]`.
            while argv and (argv[0] in KEYWORDS or ASSIGN.match(argv[0])):
                argv.pop(0)
            # `command [-p] [--] cmd …` runs cmd; `command -v/-V cmd` only looks it up.
            while argv and argv[0] == "command":
                argv.pop(0)
                while argv and argv[0].startswith("-"):
                    opt = argv.pop(0)
                    if opt == "--":
                        break
                    if "v" in opt or "V" in opt:
                        argv = []
            chdir = None
            if argv and argv[0] == "env":
                argv.pop(0)
                while argv and (argv[0].startswith("-") or ASSIGN.match(argv[0])):
                    if argv[0] in ("-C", "--chdir") and len(argv) > 1:
                        chdir = argv[1]
                    elif argv[0].startswith("--chdir="):
                        chdir = argv[0].split("=", 1)[1]
                    del argv[:2 if argv[0] in ("-u", "-C", "--chdir") else 1]
            if argv:
                # `env -C DIR cmd` is `(cd DIR && cmd)`: the subshell bounds scope the cd to that one command.
                yield from ([["("], ["cd", chdir], argv, [")"]] if chdir else [argv])
            argv = []
            # Subshell bounds go through as their own segments so callers can scope `cd`.
            yield from ([c] for c in t if c in "()")
        else:
            argv.append(t.translate(UNHIDE))


def walk(cmd, cwd):
    """Yield (dir, argv) for each non-cd segment, tracking `cd DIR` and subshell bounds.

    A dir containing `$` or a backtick can't be resolved statically; it is yielded
    as-is so the caller can refuse or skip it.
    """
    stack = []
    for argv in segments(cmd):
        if argv == ["("]:
            stack.append(cwd)
        elif argv == [")"]:
            cwd = stack.pop() if stack else cwd
        elif argv[0] in ("cd", "pushd", "popd"):
            # cd [-L|-P [-e]] [-@] [--] dir: the operand is the first non-option word. A bare `cd` ($HOME),
            # `cd -` ($OLDPWD) and pushd/popd (the dir stack) go where the guard can't see: left unresolved.
            d = next((a for a in argv[1:] if not a.startswith("-")), None)
            if argv[0] != "cd":
                d = "$DIRSTACK"
            elif "-" in argv[1:]:
                d = "$OLDPWD"
            elif d is None:
                d = "$HOME"
            cwd = d if "$" in d else os.path.join(cwd, os.path.expanduser(d))
        else:
            yield cwd, argv


def sync_calls(cmd, cwd):
    """Yield (dir, subcommand, refs) for each git merge/pull/rebase that names a ref.

    Tracks `cd DIR` (via walk) and `git -C DIR`.
    """
    for cwd, argv in walk(cmd, cwd):
        if argv[0] != "git":
            continue
        d, i = cwd, 1
        while i < len(argv) and argv[i].startswith("-"):
            if argv[i] == "-C" and i + 1 < len(argv):
                d = argv[i + 1] if "$" in argv[i + 1] else os.path.join(d, os.path.expanduser(argv[i + 1]))
                i += 2
            elif argv[i] == "-c":
                i += 2
            else:
                i += 1
        if i >= len(argv) or argv[i] not in SYNC_SUBCOMMANDS:
            continue
        sub, rest, refs, skip = argv[i], argv[i + 1:], [], False
        if CONTROL_FLAGS & set(rest):
            continue
        for a in rest:
            if skip:
                skip = False
            elif a in FLAGS_WITH_VALUE:
                skip = True
            elif not a.startswith("-"):
                refs.append(a)
        if refs:
            yield d, sub, refs


def names_base(refs, base):
    """True when a ref spells the PR base: bare, refs/heads/, <remote>/ or refs/remotes/<remote>/.

    ponytail: string match, not commit resolution; a local branch named `x/<base>`
    also matches (the block is overridable). Resolve with rev-parse if that bites.
    """
    for r in refs:
        r = r.removeprefix("refs/heads/")
        if r.startswith("refs/remotes/"):
            r = r.removeprefix("refs/remotes/")
        if r == base or (r.endswith("/" + base) and "/" not in r[:-len(base) - 1]):
            return True
    return False


def pr_state(d):
    """Return (baseRefName, mergeStateStatus) for the open PR of d's branch, or None."""
    try:
        branch = subprocess.run(["git", "-C", d, "rev-parse", "--abbrev-ref", "HEAD"],
                                capture_output=True, text=True, timeout=5).stdout.strip()
        if not branch or branch == "HEAD":
            return None
        for attempt in range(2):
            out = subprocess.run(
                ["gh", "pr", "view", branch, "--json", "state,baseRefName,mergeStateStatus"],
                cwd=d, capture_output=True, text=True, timeout=8)
            if out.returncode != 0:
                return None
            pr = json.loads(out.stdout)
            if pr.get("state") != "OPEN":
                return None
            # GitHub computes mergeability lazily; the first read is often UNKNOWN.
            if pr.get("mergeStateStatus") != "UNKNOWN" or attempt:
                return pr["baseRefName"], pr["mergeStateStatus"]
            time.sleep(2)
    except (OSError, subprocess.SubprocessError, ValueError, KeyError):
        return None


GH_ALIASES = {"new": "create"}


def gh_words(argv):
    """Return (positional words, has_repo_flag) for a `gh` call, else None.

    `-R/--repo` is inherited, so it may come before the command group.
    """
    if argv[0] != "gh":
        return None
    pos, has_repo, skip = [], False, False
    for a in argv[1:]:
        if skip:
            skip = False
        elif a in ("-R", "--repo"):
            has_repo = skip = True
        elif a.startswith("--repo=") or (a.startswith("-R") and len(a) > 2):
            has_repo = True
        elif not a.startswith("-"):
            pos.append(a)
    return pos, has_repo


def gh_pr(argv):
    """Return (subcommand, has_repo_flag) for a `gh pr <sub>` call, else None. `new` is an alias of `create`."""
    words = gh_words(argv)
    if not words or len(words[0]) < 2 or words[0][0] != "pr":
        return None
    return GH_ALIASES.get(words[0][1], words[0][1]), words[1]


# Any at-mention of the Codex bot starts a Codex task on Matt's quota (Program Cop, 2026-11-19).
CODEX_MENTION = re.compile(r"(?<![\w.+-])@codex(?![\w-])", re.I)  # not an email like bob@codex.io
# Commands that post a comment body: (words, flags whose value is a file holding the body).
COMMENT_POSTS = {("pr", "comment"): ("-F", "--body-file"), ("issue", "comment"): ("-F", "--body-file"),
                 ("pr", "review"): ("-F", "--body-file")}
API_FIELD_FLAGS = ("-f", "--raw-field", "-F", "--field")
MAX_BODY_FILE = 1 << 20


def _body_file(d, path):
    """Text of a body file, or None when it can't be read (stdin, a $-path, missing, binary)."""
    if path == "-" or "$" in path or "`" in path or "$" in d or "`" in d:
        return None
    try:
        with open(os.path.join(d, os.path.expanduser(path)), "rb") as f:
            return f.read(MAX_BODY_FILE).decode("utf-8", "replace")
    except OSError:
        return None  # unreadable: the raw-command search in codex_mention_post still applies


def codex_mention_post(cmd, cwd):
    """True when the command posts a comment (gh pr/issue comment, gh pr review, gh api) whose body
    mentions the Codex bot: in an argument, in a readable body file, or on stdin when the raw command
    holds the mention (a heredoc fed to `--body-file -`, which strip_comments_and_heredocs drops)."""
    for d, argv in walk(cmd, cwd):
        words = gh_words(argv)
        if not words:
            continue
        pos = words[0]
        if tuple(pos[:2]) in COMMENT_POSTS:
            file_flags = COMMENT_POSTS[tuple(pos[:2])]
        elif pos[:1] == ["api"]:
            file_flags = ("--input",)
        else:
            continue
        api = pos[0] == "api"
        # gh api: only the request body (fields and --input) posts; a --jq filter or path does not
        texts, files = ([] if api else list(argv)), []
        for i, a in enumerate(argv):
            if re.match(r"-[A-Za-z].", a):  # pflag shorthand with an attached value: -Ffile, -fbody=x, -F=file
                name, value = a[:2], a[2:].removeprefix("=")
            else:
                name, eq, value = a.partition("=")
                value = value if eq else (argv[i + 1] if i + 1 < len(argv) else "")
            if name in file_flags:
                files.append(value)
            elif api and name in API_FIELD_FLAGS:
                texts.append(value)
                if name in ("-F", "--field") and "=@" in value:  # -F body=@file reads the field from a file
                    files.append(value.split("=@", 1)[1])
        # A body file may be written earlier in this same command (`cat > b.md <<EOF … && gh … -F b.md`) or be
        # stdin (`-`, /dev/stdin, /dev/fd/0), so the hook can't read what will be posted: any mention anywhere
        # in the command blocks. Otherwise the file as it stands now is scanned.
        if files and CODEX_MENTION.search(cmd):
            return True
        texts += [_body_file(d, path) or "" for path in files]
        if any(CODEX_MENTION.search(t) for t in texts):
            return True
    return False


def flag_on(argv, names):
    """A gh (pflag) bool flag is on when bare (`--draft`, `-d`) or given a true value (`--draft=true`, `-d=1`).

    pflag is last-wins: `--disable-auto --disable-auto=false` leaves it off, so the last occurrence decides.
    """
    on = False
    for a in argv:
        name, eq, value = a.partition("=")
        if name in names:
            on = not eq or value.lower() in ("true", "t", "1")
    return on


def draft_violation(cmd):
    for argv in segments(cmd):
        pr = gh_pr(argv)
        if not pr:
            continue
        if pr[0] == "create" and flag_on(argv, ("--draft", "-d")):
            return True
        if pr[0] == "ready" and flag_on(argv, ("--undo",)):
            return True
    return False


def draft_mode(prefs=None):
    """True when aec's settings.pr_open_mode is "draft"; anything else means ready."""
    prefs = prefs or Path.home() / ".agents-environment-config" / "preferences.json"
    try:
        return json.loads(prefs.read_text())["settings"]["pr_open_mode"] == "draft"
    except (OSError, ValueError, KeyError, TypeError):
        return False


def pr_create_dirs(cmd, cwd):
    """Yield the effective dir of each `gh pr create` that has no -R/--repo."""
    for d, argv in walk(cmd, cwd):
        if gh_pr(argv) == ("create", False):
            yield d


def unpinned_fork(cwd):
    """Return 'owner/repo (fork of parent)' when cwd is a fork with no gh default repo."""
    try:
        if subprocess.run(["gh", "repo", "set-default", "--view"], cwd=cwd,
                          capture_output=True, text=True, timeout=8).stdout.strip():
            return None
        out = subprocess.run(["gh", "repo", "view", "--json", "nameWithOwner,isFork,parent"],
                             cwd=cwd, capture_output=True, text=True, timeout=8)
        r = json.loads(out.stdout) if out.returncode == 0 else {}
        if r.get("isFork") and r.get("parent"):
            p = r["parent"]
            return f"{r['nameWithOwner']} (fork of {p['owner']['login']}/{p['name']})"
    except (OSError, subprocess.SubprocessError, ValueError, KeyError, TypeError):
        return None
    return None


GREEN = {"SUCCESS", "SKIPPED", "NEUTRAL"}
MERGE_FLAGS_WITH_VALUE = {"-t", "-b", "-F", "-A", "-R", "--subject", "--body", "--body-file",
                          "--author-email", "--match-head-commit", "--repo"}
STATUS_QUERY = re.compile(r"^gh\b.*\b(pr (checks|view|status)|run (view|watch|list))\b")


def merge_args(argv):
    """Tokenize a `gh ... pr merge` call once, the way gh does: (ref, flag tokens, repo).

    Every reader of a merge call goes through here, so a value is never read as a flag. Value flags
    (MERGE_FLAGS_WITH_VALUE) consume the next token whatever it looks like (`--body --repo=x` is a body).
    Flag tokens keep their `=value` so callers can test them with flag_on(). repo is the last
    `-R/--repo` value (as in gh), '' when none, None when unsure: only `-R x`, `--repo x`, `--repo=x`
    and `-Rowner/repo` are trusted; any other multi-letter short-flag token (`-dR x`, `-st 5 6`, `-Rd`)
    or a trailing `-R` returns None so the caller fails closed (pflag clusters are open-ended).
    """
    ref, toks, repo, past_merge, value_of = "", [], "", False, None
    for a in argv[1:]:
        if value_of:
            if value_of in ("-R", "--repo"):
                repo = a
            elif value_of == "--match-head-commit":
                toks[-1] = f"--match-head-commit={a}"
            value_of = None
        elif a in MERGE_FLAGS_WITH_VALUE:
            toks.append(a)
            value_of = a
        elif a.startswith("--repo="):
            toks.append("--repo")
            repo = a[len("--repo="):]
        elif re.fullmatch(r"-R=?[^-/=\s][^/\s]*/[^/\s]+", a):
            toks.append("-R")
            repo = a[2:].lstrip("=")
        elif re.match(r"-[^-]", a) and len(a) > 2:
            repo = None
            break
        elif a.startswith("-"):
            toks.append(a)
        elif not past_merge:
            past_merge = a == "merge"
        elif not ref:
            ref = a
    if value_of in ("-R", "--repo"):
        repo = None
    return ref, toks, repo


def merge_calls(cmd, cwd):
    """Yield (dir, ref, flag tokens, repo) for each `gh pr merge`, dir after any `cd`/`env -C`; see merge_args()."""
    # A `cd` in a background job or pipeline stage (`cd x & gh …`, `cd x |& gh …`) doesn't reach the
    # merge, but walk() can't see operators: once the dir has moved, any of them makes it unresolved.
    async_op = runs_async(cmd)
    for d, argv in walk(cmd, cwd):
        pr = gh_pr(argv)
        if pr and pr[0] == "merge":
            yield ("$UNRESOLVED" if async_op and d != cwd else d, *merge_args(argv))

RUN_ID = re.compile(r"/actions/runs/(\d+)/job/(\d+)")
# All gh calls of one merge check share this budget, under the hook's 20 s timeout_ms (hooks.json):
# a per-run jobs lookup that would overrun it is skipped, and that run supersedes nothing (fail closed).
GH_BUDGET_S = 15


def _left(deadline, cap):
    """Seconds a gh call may take: at most cap, never past the shared deadline; None when spent."""
    left = min(cap, deadline - time.monotonic())
    return left if left >= 1 else None


def green(e):
    # Check runs carry `conclusion` (empty while running); status contexts carry `state`.
    return (e.get("conclusion") or e.get("state") or "").upper() in GREEN


PR_URL = re.compile(r"https?://([^/]+)/([^/]+/[^/]+)/pull/\d+")
GATE_TITLE = re.compile(r"Review Gate - PR #(\d+)")  # review-gate 3.2.6+ run-name


def _api_lines(pr, path, jq, cwd, deadline):
    """`gh api --paginate` against the selected PR's own host and repo, parsed from its URL, so a URL
    selector or an Enterprise -R never falls back to the cwd's repo (#90 Codex P2). One JSON value per
    line, never @tsv, whose escapes would not match the rollup's names (#90 Codex P2). None = unknown."""
    m = PR_URL.fullmatch(pr.get("url") or "")
    timeout = _left(deadline, 15)
    if not m or timeout is None:
        return None
    try:
        out = subprocess.run(["gh", "api", "--hostname", m.group(1), "--paginate", f"repos/{m.group(2)}/{path}",
                              "--jq", f"{jq} | tojson"], cwd=cwd, capture_output=True, text=True, timeout=timeout)
        return [json.loads(line) for line in out.stdout.splitlines()] if out.returncode == 0 else None
    except (OSError, subprocess.SubprocessError, ValueError):
        return None


def run_workflows(pr, cwd, deadline):
    """Map each Actions run id on the head that belongs to THIS PR to (workflow file path, event);
    {} when unknown (fail closed: unresolved runs supersede nothing, so every entry must be green).

    Two PRs can share a head sha (one branch into staging and main), and every run on that sha is in
    the rollup. A run belongs to this PR only when its pull_requests list is exactly this PR, its head
    branch and repo are this PR's, and a review-gate run-name names no other PR. A run listing several
    PRs, or none (forks), is ambiguous and supersedes nothing (nevar-fund#27 Codex P1 r4582757746)."""
    sha, number = pr.get("headRefOid") or "", pr.get("number")
    if not re.fullmatch(r"[0-9a-f]{40}", sha):
        return {}
    rows = _api_lines(pr, f"actions/runs?head_sha={sha}&per_page=100",
                      '.workflow_runs[] | [.id, .path, .event, [.pull_requests[].number], .display_title, .head_branch,'
                      ' (.head_repository.full_name // "")]', cwd, deadline)
    head = [pr.get("headRefName"), (pr.get("headRepository") or {}).get("nameWithOwner")]
    mine = {}
    for run_id, path, event, prs, title, branch, repo in (r for r in rows or [] if len(r) == 7):
        gate = GATE_TITLE.fullmatch(title or "")
        if path and prs == [number] and [branch, repo] == head and not (gate and int(gate.group(1)) != number):
            mine[str(run_id)] = (path, event)
    return mine


def run_jobs(run_id, pr, cwd, deadline):
    """Map each real job of an Actions run (all attempts) to (name, conclusion); {} when unknown.

    detailsUrl is writable by anyone with Checks write access, so a custom check can point at a
    legitimate run. Only an entry whose job id is a real job of that run, with the same name and
    conclusion, is that job (claude-skills#90 Codex P1 r4582487271). Out of budget (#90 Codex P2
    r4582534724) or a failed call resolves nothing."""
    rows = _api_lines(pr, f"actions/runs/{run_id}/jobs?filter=all&per_page=100",
                      '.jobs[] | [.id, .name, (.conclusion // "")]', cwd, deadline)
    return {str(r[0]): (r[1], (r[2] or "").upper()) for r in rows or [] if len(r) == 3}


def not_green(ref, repo="", cwd=None):
    """Return '' when every check on the PR is green, else a description of why not.

    cwd is the merge's effective dir: without -R, gh resolves the PR number in that dir's repo.
    With -R the dir doesn't matter, so an unresolved one is ignored.
    """
    if repo:
        cwd = None
    elif cwd and ("$" in cwd or "`" in cwd):
        return f"can't resolve the merge's working directory ({cwd}); pass -R owner/repo"
    deadline = time.monotonic() + GH_BUDGET_S
    try:
        out = subprocess.run(["gh", "pr", "view", *([ref] if ref else []), *(["-R", repo] if repo else []), "--json",
                              "statusCheckRollup,mergeStateStatus,headRefOid,number,url,headRefName,headRepository"],
                             cwd=cwd, capture_output=True, text=True, timeout=8)
        if out.returncode != 0:
            return f"gh failed: {out.stderr.strip()}"
        view = json.loads(out.stdout)
        rollup = view.get("statusCheckRollup") or []
    except (OSError, subprocess.SubprocessError, ValueError, AttributeError) as e:
        return f"gh failed: {e}"
    if not rollup:
        return "no checks reported yet"
    workflows = run_workflows(view, cwd, deadline)
    # The rollup lists every workflow run on the head: a PR whose first Review Gate run failed
    # (body lacked `## Review`) keeps that red run after a newer run goes green. GitHub already
    # collapses re-attempts *within* a run (only the latest attempt is listed), so identity is the
    # run id in detailsUrl (/actions/runs/<run>/job/<job>), not the name. Per (workflow, job name),
    # the newest run supersedes older runs (by the run's first startedAt over all its jobs, ISO-8601 UTC), and every
    # same-named job inside that run is a distinct job that must be green on its own: a later green
    # job (e.g. one with `needs:`) never hides an earlier failed sibling. Runs tied on startedAt
    # cannot be ordered, so all of them count (fail closed). The workflow is identified by the run's
    # file path and event from the Actions API, never by the editable `name:` (a PR can add a workflow
    # named `CI` whose green job would otherwise supersede the real CI failure), and an entry counts as
    # that run's job only when the Actions jobs API lists its job id in that run with the same name
    # and conclusion (detailsUrl is writable, so a custom check could claim any run). Status contexts,
    # third-party check runs, another PR's runs on a shared head sha, and any entry without startedAt
    # or a run id resolved to a workflow path of THIS PR are never collapsed and must be green on their own.
    groups, latest, run_start, jobs = {}, [], {}, {}
    for e in rollup:
        # gh serializes a missing startedAt as the zero time "0001-01-01T00:00:00Z", not null
        m = RUN_ID.search(e.get("detailsUrl") or "")
        # No parsable run id: run identity is unknown, so the entry supersedes nothing (fail closed).
        if m and m.group(1) in workflows and m.group(1) not in jobs:
            jobs[m.group(1)] = run_jobs(m.group(1), view, cwd, deadline)
        if (m and m.group(1) in workflows and (e.get("startedAt") or "") > "0002"
                and jobs[m.group(1)].get(m.group(2)) == (e.get("name"), (e.get("conclusion") or "").upper())):
            run_key = m.group(1)
            # A run starts when its first job does, across ALL its jobs: a dependency-delayed job
            # in an older run must not make that run outrank a newer one.
            run_start[run_key] = min(run_start.get(run_key, e["startedAt"]), e["startedAt"])
            groups.setdefault((workflows[run_key], e.get("name")), {}).setdefault(run_key, []).append(e)
        else:
            latest.append(e)
    for runs in groups.values():
        newest = max(run_start[k] for k in runs)
        latest += [e for k, es in runs.items() if run_start[k] == newest for e in es]
    bad = [f"{e.get('name') or e.get('context')}: {(e.get('conclusion') or e.get('state') or 'PENDING').upper()}"
           for e in latest if not green(e)]
    return ", ".join(bad)


def polls(cmd):
    segs = list(segments(cmd))
    return (any(a[0] == "sleep" for a in segs)
            and any(STATUS_QUERY.match(" ".join(a)) for a in segs))


def check(cmd, cwd):
    """Return a block message, or None to allow."""
    if polls(cmd):
        return ("Blocked: never poll: run `gh pr checks <n> --watch --fail-fast` in the background "
                "and let the harness wake you.")
    if codex_mention_post(cmd, cwd) and not has_override(cmd, "codex-review-ok"):
        return ("Blocked: this comment mentions the Codex bot, which starts a Codex review on Matt's quota. "
                "Codex reviews a PR's first head only. For a later head, run a fallback reviewer and add "
                "`Fallback review: <reviewer> on <sha> — verdict: <clean|findings fixed>` to the PR's "
                "## Review section. Only when Matt explicitly asked for a Codex review here, add "
                "`# codex-review-ok: <reason>` (the colon is optional) to the command.")
    for d, ref, toks, repo in merge_calls(cmd, cwd):
        if repo is None:
            return ("Blocked: can't parse this merge (a short-flag cluster such as `-dR x` or `-st 5`). "
                    "Spell each flag separately and pass the repo as a standalone `-R owner/repo`.")
        if flag_on(toks, ("--admin",)):
            return "Blocked: never bypass required checks with --admin; fix the red check or ask Matt."
        if flag_on(toks, ("--auto",)):
            return ("Blocked: never `--auto`: Review Gate does not re-run on late review or thread events, "
                    "so auto-merge can land a PR a late P2 should have stopped. Hand the PR to the repo's "
                    f"traffic cop, which merges with `gh pr merge {ref or '<n>'} --squash --match-head-commit <sha>` "
                    "(`--merge` for promotions into main).")
        # merges nothing: cancels an enabled auto-merge (--admin/--auto blocked above). Only when on:
        # `--disable-auto=false` leaves the option off, so that call merges and takes the full checks.
        if flag_on(toks, ("--disable-auto",)):
            continue
        heads = [t.partition("=")[2] for t in toks if t.partition("=")[0] == "--match-head-commit"]
        if not heads or not re.fullmatch(r"[0-9a-f]{40}", heads[-1]):
            return (f"Blocked: pin the reviewed head with its full 40-hex SHA: `gh pr merge {ref or '<n>'} --squash --match-head-commit <sha>` "
                    "(`--merge` for promotions into main), so a push after review cannot be merged unreviewed.")
        why = not_green(ref, repo, d)
        if why:
            return (f"Blocked: checks are not all green for {ref or 'this branch'} ({why}): "
                    "wait for them (`gh pr checks <n> --watch --fail-fast` in the background) or fix the red "
                    "check, then merge.")
    if draft_violation(cmd) and not draft_mode():
        return ("Blocked: PRs open ready for review, never as drafts. Drop --draft / --undo. "
                "If the user explicitly asked for a draft, ask them to run it with `! gh pr create --draft ...`, "
                "or set aec's pr_open_mode to draft.")
    for d in pr_create_dirs(cmd, cwd):
        # A dir with $ or a backtick can't be resolved statically: skip, don't block.
        fork = None if "$" in d or "`" in d else unpinned_fork(d)
        if fork:
            return (f"Blocked: {fork} has no `gh repo set-default`, so `gh pr create` would open the "
                    "PR on the upstream repo. Pass `-R <owner>/<repo>` or run "
                    "`gh repo set-default <owner>/<repo>` first.")
    if any(re.match(r"#\s*sync-base:", c) for c in shell_comments(cmd)):  # a real shell comment, not quoted text
        return None
    for d, sub, refs in sync_calls(cmd, cwd):
        if "$" in d or "`" in d:
            return (f"Blocked: `git {sub}` runs in a directory the guard can't resolve ({d}). "
                    "Don't sync the base into every worktree in a loop: most of those PRs are already "
                    "mergeable, and each sync restarts their CI and review. Run it per worktree with a "
                    "literal path so each PR is checked, or add `# sync-base: <reason>` if you need a "
                    "specific base commit.")
        state = pr_state(d)
        if not state:
            continue
        base, status = state
        if names_base(refs, base) and status in MERGEABLE:
            return (f"Blocked: this branch's PR into `{base}` is {status}, so GitHub can already merge it. "
                    f"Pulling `{base}` in restarts CI and review for nothing. Sync only when "
                    "`gh pr view --json mergeStateStatus` says DIRTY (a conflict). To land the PR: "
                    "hand it to the repo's traffic cop: `gh pr merge <n> --squash --match-head-commit <sha>` (or `--merge` for promotions). If you truly need "
                    f"a commit from `{base}` (a fix your tests depend on), add `# sync-base: <reason>`.")
    return None


def main():
    try:
        data = json.load(sys.stdin)
    except ValueError:
        return 0
    if data.get("tool_name") != "Bash":
        return 0
    msg = check(data.get("tool_input", {}).get("command", ""), data.get("cwd") or os.getcwd())
    if msg:
        print(msg, file=sys.stderr)
        return 2
    return 0

def fb_log(subject: str, severity: str, summary: str) -> None:
    """Best-effort feedback-loop capture: a missing or failing store never affects this hook."""
    import os
    import subprocess
    candidates = [os.environ.get("AGENT_FEEDBACK_BIN"),
                  Path(os.environ.get("CLAUDE_PROJECT_DIR", ".")) / ".claude/skills/feedback-loop/scripts/feedback.py",
                  Path.home() / ".claude/skills/feedback-loop/scripts/feedback.py"]
    for c in candidates:
        if c and Path(c).is_file():
            try:
                subprocess.Popen(["python3", str(c), "log", subject, "--reporter", "hook",
                                  "--severity", severity, "--summary", summary, "--quiet"],
                                 stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                 stderr=subprocess.DEVNULL, start_new_session=True)
            except OSError:
                pass  # best-effort by design: feedback must never break the hook
            return


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        fb_log("hook:pr-merge-flow/pmf-pr-guard", "high", f"pr-guard crashed: {type(exc).__name__}")
        raise
