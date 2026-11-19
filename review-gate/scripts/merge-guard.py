#!/usr/bin/env python3
"""PreToolUse guard: block gh pr merge when review-gate checks fail.

Exit 0 = allow. Exit 2 = block (stderr message for the agent).
Override: include `# review-gate-ok: <reason>` in the Bash command.
"""
from __future__ import annotations

import importlib.util
import json
import os
import re
import shlex
import subprocess
import sys
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    "check_review_gate", Path(__file__).resolve().with_name("check-review-gate.py")
)
gate = importlib.util.module_from_spec(_spec)
try:
    _spec.loader.exec_module(gate)
except BaseException as _exc:  # noqa: BLE001 - a missing/broken gate module must block, not exit 1 (non-blocking)
    print(f"review-gate merge guard: cannot load check-review-gate.py ({type(_exc).__name__}); blocked", file=sys.stderr)
    sys.exit(2)

OVERRIDE = re.compile(r"#\s*review-gate-ok:\s*\S")
# Loose detector; `is_gh_pr_merge` confirms token order (allows `gh pr -R … merge`).
# Hyphen-aware word edges: `pr-merge-flow` is a skill name, not `pr … merge`.
MERGE_RE = re.compile(r"(?<![\w-])gh(?![\w-]).*(?<![\w-])pr(?![\w-]).*(?<![\w-])merge(?![\w-])", re.S)
# Quote-smashed executable: Bash concatenates `g''h` / `g"h"` into `gh`.
QUOTE_SMASHED_GH_RE = re.compile(r"g['\"]+h", re.I)
# ``NAME=value``, ``NAME+=value``, and indexed ``NAME[0]=value`` / ``PATH[0]=…``.
ASSIGNMENT_RE = re.compile(
    r"^([A-Za-z_][A-Za-z0-9_]*(?:\[[^\]]*\])?)(?:\+)?=(.*)$"
)
# Pull *URL* selectors must include a scheme (gh treats scheme-less paths as branch names).
# Groups: host, owner, repo, number. Optional query/fragment/trailing path (gh accepts them).
PULL_URL = re.compile(
    r"https?://(?:www\.)?([^/\s]+)/([^/]+)/([^/]+)/pull/(\d+)(?:[/?#][^\s]*)?",
    re.I,
)
DOTCOM_PULL_HOSTS = frozenset({"github.com", "www.github.com"})
# Subshell `(cd` / `(pushd` / `(popd` — cwd change we refuse to model without -R.
SUBSHELL_CD_RE = re.compile(r"\(\s*(cd|pushd|popd)\b", re.I)
# Optional ``if``/``while``/``until`` before a definition (condition position).
_CTRL_FLOW_DEF_PREFIX = r"(?:(?:if|while|until)\s+)?"
# Lead: line/chain start, brace-group ``{``, or a ``case`` arm closer ``)``.
# Brace groups keep definitions in the current shell (``{ gh(){…;}; }; gh …``).
_DEF_LEAD = rf"(?:^|[\n;&|{{]|(?<=\)))\s*{_CTRL_FLOW_DEF_PREFIX}"
# Shell redefinitions that shadow the external ``gh`` binary / prefix builtins.
GH_FUNC_RE = re.compile(
    rf"{_DEF_LEAD}(?:function\s+gh\b|gh\s*\(\s*\))",
    re.I,
)
# Local ``command_not_found_handle(){…}`` / ``function command_not_found_handle``.
CNF_FUNC_RE = re.compile(
    rf"{_DEF_LEAD}"
    r"(?:function\s+command_not_found_handle\b|"
    r"command_not_found_handle\s*\(\s*\))",
    re.I,
)
# ``alias gh=…`` / ``builtin alias`` / ``builtin builtin alias`` / ``command alias``
GH_ALIAS_RE = re.compile(
    rf"{_DEF_LEAD}"
    r"(?:(?:builtin|command)\s+)*alias(?:\s+(?:--|-[\w]+))*\s+gh=",
    re.I,
)
# ``hash -p … gh`` / ``builtin hash`` / ``builtin builtin hash`` / ``command hash``
GH_HASH_RE = re.compile(
    rf"{_DEF_LEAD}"
    r"(?:(?:builtin|command)\s+)*hash\s+[^\n;&|]*\bgh\b",
    re.I,
)
# Wrappers/prefixes stripped before ``gh`` that Bash also allows as functions.
SHADOWABLE_PREFIXES = frozenset({"command", "builtin", "exec", "time", "env"})
PREFIX_FUNC_RE = re.compile(
    rf"{_DEF_LEAD}"
    r"(?:function\s+(?:command|builtin|exec|time|env)\b|"
    r"(?:command|builtin|exec|time|env)\s*\(\s*\))",
    re.I,
)
PREFIX_ALIAS_RE = re.compile(
    rf"{_DEF_LEAD}"
    r"(?:(?:builtin|command)\s+)*alias(?:\s+(?:--|-[\w]+))*\s+"
    r"(?:command|builtin|exec|time|env)=",
    re.I,
)
# Value-taking flags from `gh pr merge --help` (and shared -R/--repo).
# Walk argv and consume their values so body text cannot fake a -R match.
MERGE_VALUE_FLAGS = frozenset(
    {
        "--match-head-commit",
        "--body",
        "-b",
        "--body-file",
        "-F",
        "--subject",
        "-t",
        "--author-email",
        "-A",
        "-R",
        "--repo",
    }
)
# Single-letter value-taking flags (cobra/pflag bundles: `-dR owner/repo`).
MERGE_VALUE_SHORT = frozenset({"R", "b", "F", "t", "A"})
# Separators that do not guarantee a preceding `cd` applied to the parent shell.
CONDITIONAL_SEPS = frozenset({"||", "|", "&"})


def _consume_merge_argv_flag(
    tokens: list[str], i: int
) -> tuple[int, str | None, bool]:
    """Advance past a merge argv flag at ``tokens[i]``.

    Returns ``(next_index, repo_from_-R_or_None, missing_value)``.
    Understands cobra-style short clusters (``-dR owner/target``, ``-dRowner/target``)
    so a bundled ``R`` is not skipped as an unknown boolean flag.
    """
    tok = tokens[i]
    if tok in ("-R", "--repo"):
        if i + 1 >= len(tokens):
            return i + 1, None, True
        return i + 2, tokens[i + 1], False
    if tok.startswith("--repo="):
        return i + 1, tok.split("=", 1)[1], False
    if tok.startswith("--"):
        if "=" in tok:
            return i + 1, None, False
        if tok in MERGE_VALUE_FLAGS:
            if i + 1 >= len(tokens):
                return i + 1, None, True
            return i + 2, None, False
        return i + 1, None, False
    if not tok.startswith("-") or tok == "-":
        return i + 1, None, False
    # Short option or cluster: -Rowner, -bTEXT, -dR owner, -dRowner, -b, …
    if "=" in tok:
        # ``-R=owner/repo`` / ``-b=text`` (unlikely for gh, but consume as one token).
        key, _, val = tok[1:].partition("=")
        if key == "R":
            return i + 1, val, False
        return i + 1, None, False
    body = tok[1:]
    j = 0
    while j < len(body):
        ch = body[j]
        if ch in MERGE_VALUE_SHORT:
            attached = body[j + 1 :]
            if attached:
                value = attached
                next_i = i + 1
            else:
                if i + 1 >= len(tokens):
                    return i + 1, None, True
                value = tokens[i + 1]
                next_i = i + 2
            if ch == "R":
                return next_i, value, False
            return next_i, None, False
        j += 1
    return i + 1, None, False


def _shell_tokens(cmd: str) -> list[str]:
    try:
        return shlex.split(cmd, posix=True)
    except ValueError:
        return cmd.split()


def shell_comments(cmd: str) -> list[str]:
    """Return `#…` shell comments at depth 0 (not quotes / `<(…)` / `$(…)` / backticks)."""
    comments: list[str] = []
    i = 0
    in_single = False
    in_double = False
    depth = 0
    n = len(cmd)
    while i < n:
        c = cmd[i]
        if in_single:
            if c == "'":
                in_single = False
            i += 1
            continue
        if in_double:
            if c == "\\" and i + 1 < n:
                i += 2
                continue
            if c == '"':
                in_double = False
            i += 1
            continue
        if c == "'":
            in_single = True
            i += 1
            continue
        if c == '"':
            in_double = True
            i += 1
            continue
        # Legacy backtick command substitution — skip until closing unescaped `.
        if c == "`":
            i += 1
            while i < n:
                if cmd[i] == "\\" and i + 1 < n:
                    i += 2
                    continue
                if cmd[i] == "`":
                    i += 1
                    break
                i += 1
            continue
        # Nested process / command substitutions and subshells.
        if c in "<>" and i + 1 < n and cmd[i + 1] == "(":
            depth += 1
            i += 2
            continue
        if c == "$" and i + 1 < n and cmd[i + 1] == "(":
            depth += 1
            i += 2
            continue
        if c == "(":
            depth += 1
            i += 1
            continue
        if c == ")" and depth > 0:
            depth -= 1
            i += 1
            continue
        if depth == 0 and _is_unescaped_shell_comment_hash(cmd, i):
            end = cmd.find("\n", i)
            if end < 0:
                end = n
            comments.append(cmd[i:end])
            i = end
            continue
        i += 1
    return comments


def _is_unescaped_shell_comment_hash(cmd: str, i: int) -> bool:
    """True when ``cmd[i]`` is ``#`` starting a real shell comment (not ``\\ #``)."""
    if i < 0 or i >= len(cmd) or cmd[i] != "#":
        return False
    if i == 0:
        return True
    if not cmd[i - 1].isspace():
        return False
    # Odd number of backslashes immediately before that whitespace → escaped space.
    bs = 0
    k = i - 2
    while k >= 0 and cmd[k] == "\\":
        bs += 1
        k -= 1
    return bs % 2 == 0


def segment_has_override(part: str) -> bool:
    """True when `# review-gate-ok:` is a shell comment on this merge segment."""
    if not is_gh_pr_merge(part):
        return False
    return any(OVERRIDE.search(c) for c in shell_comments(part))


def has_override(cmd: str) -> bool:
    """True when any merge segment carries `# review-gate-ok:`.

    Overrides must be attached to the ``gh pr merge`` invocation itself — not
    buried in heredoc data or a prior unrelated line. Each merge segment is
    evaluated independently (an override on one does not waive others).
    """
    chains = split_shell_chains(cmd)
    parts = [p for p, _ in chains] if chains else [cmd]
    return any(segment_has_override(p) for p in parts)


def _parse_heredoc_delimiter(cmd: str, j: int) -> tuple[str, int, bool] | None:
    """Parse a Bash heredoc word with quote removal.

    Bash forms the closing delimiter by quote-removing the opener word, so
    ``<<E\\OF``, ``<<"E"OF``, and ``<<'EOF'`` all close on a line ``EOF``.
    Returns ``(delimiter, index_after_word, quoted)`` or ``None`` if no word.
    ``quoted`` is True when any part of the word used quotes (body not expanded).
    """
    n = len(cmd)
    if j >= n or cmd[j] in " \t\n;&|<>()":
        return None
    delim_chars: list[str] = []
    quoted = False
    while j < n:
        ch = cmd[j]
        if ch in " \t\n;&|<>()":
            break
        if ch == "'":
            quoted = True
            j += 1
            while j < n and cmd[j] != "'":
                delim_chars.append(cmd[j])
                j += 1
            if j < n and cmd[j] == "'":
                j += 1
            continue
        if ch == '"':
            quoted = True
            j += 1
            while j < n and cmd[j] != '"':
                if cmd[j] == "\\" and j + 1 < n:
                    delim_chars.append(cmd[j + 1])
                    j += 2
                    continue
                delim_chars.append(cmd[j])
                j += 1
            if j < n and cmd[j] == '"':
                j += 1
            continue
        if ch == "\\" and j + 1 < n:
            delim_chars.append(cmd[j + 1])
            j += 2
            continue
        delim_chars.append(ch)
        j += 1
    delim = "".join(delim_chars)
    if not delim:
        return None
    return delim, j, quoted


def _heredoc_feeds_shell(prefix: str) -> bool:
    """True when the command receiving the heredoc is a shell interpreter."""
    seg = prefix
    for sep in (";", "\n", "|", "&"):
        if sep in seg:
            seg = seg.rsplit(sep, 1)[-1]
    tokens = _shell_tokens(seg.strip())
    rest, _leading = _skip_leading_assignments(tokens)
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(rest):
        return False
    name = rest[i].rsplit("/", 1)[-1]
    return name in SHELL_INTERPRETERS


def _heredoc_body_has_merge(body: str) -> bool:
    """True when a heredoc body text can run or expand a ``gh pr merge``."""
    if MERGE_RE.search(body) or is_gh_pr_merge(body):
        return True
    if dynamic_gh_pr_merge(body) or quote_smashed_merge(body):
        return True
    for sub in _extract_command_substitutions(body):
        if (
            MERGE_RE.search(sub)
            or is_gh_pr_merge(sub)
            or dynamic_gh_pr_merge(sub)
            or quote_smashed_merge(sub)
        ):
            return True
    return False


def analyze_heredocs(cmd: str) -> tuple[str, list[tuple[str, bool, bool]]]:
    """Strip heredoc bodies and return ``(stripped, [(body, quoted, feeds_shell), …])``.

    Bodies are inspected before discard so ``bash <<'EOF'`` / expanding heredocs
    cannot hide a merge. Doc heredocs to ``cat`` remain strip-only.
    """
    out: list[str] = []
    infos: list[tuple[str, bool, bool]] = []
    i = 0
    in_single = False
    in_double = False
    n = len(cmd)
    while i < n:
        c = cmd[i]
        if in_single:
            out.append(c)
            if c == "'":
                in_single = False
            i += 1
            continue
        if in_double:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(cmd[i + 1])
                i += 2
                continue
            if c == '"':
                in_double = False
            i += 1
            continue
        if c == "'":
            in_single = True
            out.append(c)
            i += 1
            continue
        if c == '"':
            in_double = True
            out.append(c)
            i += 1
            continue
        if c == "\\" and i + 1 < n:
            out.append(c)
            out.append(cmd[i + 1])
            i += 2
            continue
        # Here-string <<<… — not a heredoc; keep as-is.
        if c == "<" and i + 2 < n and cmd[i + 1] == "<" and cmd[i + 2] == "<":
            out.append("<<<")
            i += 3
            continue
        # Heredoc: <<[-] WORD  (WORD may use mixed/escaped quotes; quote-removed)
        if c == "<" and i + 1 < n and cmd[i + 1] == "<":
            j = i + 2
            strip_tabs = False
            if j < n and cmd[j] == "-":
                j += 1
                strip_tabs = True
            while j < n and cmd[j] in " \t":
                j += 1
            parsed = _parse_heredoc_delimiter(cmd, j)
            if parsed is None:
                out.append(c)
                i += 1
                continue
            delim, j, quoted = parsed
            prefix = "".join(out)
            feeds_shell = _heredoc_feeds_shell(prefix)
            # Replace <<DELIM with a space, but keep the rest of the opener line
            # (e.g. `cat <<EOF; gh … pr merge` — the merge must remain visible).
            out.append(" ")
            while j < n and cmd[j] != "\n":
                out.append(cmd[j])
                j += 1
            if j < n and cmd[j] == "\n":
                j += 1
            # Collect body lines until the closing delimiter.
            body_lines: list[str] = []
            found = False
            while j < n:
                line_start = j
                while j < n and cmd[j] != "\n":
                    j += 1
                line = cmd[line_start:j]
                compare = line.lstrip("\t") if strip_tabs else line
                if compare == delim:
                    if j < n and cmd[j] == "\n":
                        j += 1
                    found = True
                    break
                body_lines.append(line)
                if j < n and cmd[j] == "\n":
                    j += 1
            if not found:
                # Unmatched opener — keep the original text so a later merge is
                # not silently swallowed with the supposed body.
                out.append(cmd[i:])
                break
            infos.append(("\n".join(body_lines), quoted, feeds_shell))
            i = j
            continue
        out.append(c)
        i += 1
    return "".join(out), infos


def strip_heredoc_bodies(cmd: str) -> str:
    """Remove heredocs so script/doc examples are not treated as merges."""
    stripped, _infos = analyze_heredocs(cmd)
    return stripped


def executable_heredoc_merge(cmd: str) -> bool:
    """True when a heredoc body that Bash executes/expands contains a merge.

    ``bash <<'EOF'`` / ``sh <<EOF`` run the body as a script. Unquoted heredocs
    expand ``$(gh … pr merge)`` even when fed to ``cat``. Quoted doc heredocs to
    non-shell commands are ignored (still stripped for false-positive avoidance).
    """
    _stripped, infos = analyze_heredocs(cmd)
    for body, quoted, feeds_shell in infos:
        if not _heredoc_body_has_merge(body):
            continue
        if feeds_shell:
            return True
        if not quoted:
            for sub in _extract_command_substitutions(body):
                if (
                    MERGE_RE.search(sub)
                    or is_gh_pr_merge(sub)
                    or dynamic_gh_pr_merge(sub)
                    or quote_smashed_merge(sub)
                ):
                    return True
    return False


def split_shell_chains(cmd: str) -> list[tuple[str, str]]:
    """Split on chain operators outside quotes.

    Returns [(segment, sep_after), ...] where sep_after is one of
    '', '&&', '||', '|', ';', '&', '\\n'.
    """
    cmd = strip_heredoc_bodies(cmd)
    parts: list[tuple[str, str]] = []
    buf: list[str] = []
    i = 0
    in_single = False
    in_double = False
    n = len(cmd)

    def flush(sep: str) -> None:
        text = "".join(buf).strip()
        buf.clear()
        if text:
            parts.append((text, sep))

    while i < n:
        c = cmd[i]
        if in_single:
            buf.append(c)
            if c == "'":
                in_single = False
            i += 1
            continue
        if in_double:
            buf.append(c)
            if c == "\\" and i + 1 < n:
                buf.append(cmd[i + 1])
                i += 2
                continue
            if c == '"':
                in_double = False
            i += 1
            continue
        if c == "'":
            in_single = True
            buf.append(c)
            i += 1
            continue
        if c == '"':
            in_double = True
            buf.append(c)
            i += 1
            continue
        # Outside quotes: backslash escapes the next char / continues a line.
        if c == "\\" and i + 1 < n:
            nxt = cmd[i + 1]
            if nxt == "\n":
                # Line continuation — do not treat the newline as a chain boundary.
                if buf and not buf[-1].isspace():
                    buf.append(" ")
                i += 2
                continue
            buf.append(c)
            buf.append(nxt)
            i += 2
            continue
        # Shell comment — keep text on the segment (for `# review-gate-ok:`) but do
        # not treat `&&` / `|` inside the comment as chain operators. Escaped
        # whitespace before `#` (e.g. `--body=\ #x; …`) is argument text, not a
        # comment — same parity as `_is_unescaped_shell_comment_hash`.
        if _is_unescaped_shell_comment_hash(cmd, i):
            while i < n and cmd[i] != "\n":
                buf.append(cmd[i])
                i += 1
            continue
        if c == "&" and i + 1 < n and cmd[i + 1] == "&":
            flush("&&")
            i += 2
            continue
        if c == "|" and i + 1 < n and cmd[i + 1] == "|":
            flush("||")
            i += 2
            continue
        if c == "|":
            flush("|")
            i += 1
            continue
        if c == ";":
            flush(";")
            i += 1
            continue
        if c == "&":
            flush("&")
            i += 1
            continue
        if c == "\n":
            flush("\n")
            i += 1
            continue
        buf.append(c)
        i += 1
    flush("")
    return parts


def _env_key_base(key: str) -> str:
    """Strip a Bash array subscript: ``PATH[0]`` → ``PATH``."""
    if "[" in key:
        return key.split("[", 1)[0]
    return key


def _assignment_is_append(tok: str) -> bool:
    """True when ``tok`` uses ``+=`` rather than plain ``=``."""
    eq = tok.find("=")
    return eq > 0 and tok[eq - 1] == "+"


def _skip_leading_assignments(tokens: list[str]) -> tuple[list[str], dict[str, str]]:
    """Strip leading VAR=value tokens; return (rest, assignments).

    Honors ``NAME+=value`` by concatenating onto a prior leading value for
    the same name (Bash append behavior).
    """
    env: dict[str, str] = {}
    i = 0
    while i < len(tokens):
        m = ASSIGNMENT_RE.match(tokens[i])
        if not m:
            break
        key = m.group(1)
        val = m.group(2)
        if _assignment_is_append(tokens[i]):
            env[key] = env.get(key, "") + val
        else:
            env[key] = val
        i += 1
    return tokens[i:], env


# Value-taking options from `env --help` that can appear before NAME=VALUE / COMMAND.
ENV_VALUE_FLAGS = frozenset(
    {
        "-C",
        "--chdir",
        "-u",
        "--unset",
        "-S",
        "--split-string",
        "--block-signal",
        "--default-signal",
        "--ignore-signal",
    }
)


# gh config location: GH_CONFIG_DIR, else $XDG_CONFIG_HOME/gh, else $HOME/.config/gh.
GH_CONFIG_LOCATION_VARS = frozenset({"GH_CONFIG_DIR", "XDG_CONFIG_HOME", "HOME"})
# Vars whose cleared (-u / -i) state the gate must mirror for host/config fidelity.
GH_TRACKED_ENV_VARS = frozenset({"GH_HOST", "GH_REPO"}) | GH_CONFIG_LOCATION_VARS


def _env_wrapper_state(
    tokens: list[str],
) -> tuple[dict[str, str], set[str]]:
    """Collect env NAME=VALUE / -u / -i effects before `gh`.

    Returns ``(assignments, cleared_names)``. Cleared names are unset for the
    child (``-u/--unset``, ``-i``, or bare ``-``) unless a later assignment
    re-sets them.
    """
    try:
        env_i = next(i for i, t in enumerate(tokens) if t == "env")
        gh_i = next(i for i, t in enumerate(tokens) if t == "gh")
    except StopIteration:
        return {}, set()
    if env_i >= gh_i:
        return {}, set()
    out: dict[str, str] = {}
    cleared: set[str] = set()
    i = env_i + 1
    while i < gh_i:
        tok = tokens[i]
        m_assign = ASSIGNMENT_RE.match(tok)
        if m_assign:
            key, val = m_assign.group(1), m_assign.group(2)
            if _assignment_is_append(tok):
                out[key] = out.get(key, "") + val
            else:
                out[key] = val
            cleared.discard(key)
            cleared.discard(_env_key_base(key))
            i += 1
            continue
        if tok.startswith("-"):
            # Bare ``-`` implies ``-i`` (GNU env).
            if tok in ("-", "-i", "--ignore-environment"):
                out.clear()
                cleared |= set(GH_TRACKED_ENV_VARS)
                i += 1
                continue
            if tok.startswith("--") and "=" in tok:
                # ``--unset=GH_HOST``
                flag, _, val = tok.partition("=")
                if flag in ("--unset", "-u"):
                    out.pop(val, None)
                    cleared.add(val)
                i += 1
                continue
            # Sticky ``-uGH_HOST`` / ``-C/path`` (no separate operand).
            if tok.startswith("-u") and tok != "-u":
                name = tok[2:]
                out.pop(name, None)
                cleared.add(name)
                i += 1
                continue
            if tok.startswith("-C") and tok != "-C":
                i += 1
                continue
            base = tok.split("=", 1)[0]
            if base in ENV_VALUE_FLAGS:
                if i + 1 >= gh_i:
                    break
                operand = tokens[i + 1]
                if base in ("-u", "--unset"):
                    out.pop(operand, None)
                    cleared.add(operand)
                i += 2
                continue
            i += 1
            continue
        break
    return out, cleared


def _direct_gh_pr_subcommand(part: str) -> str | None:
    """Return the ``gh pr <subcommand>`` verb for a ``gh`` token stream.

    Skips ``gh`` / ``pr`` flags so ``gh pr -R owner/repo merge 42`` resolves to
    ``merge`` while ``gh pr comment 42 --body merge`` resolves to ``comment``.
    Scans for a ``gh`` token (not only argv[0]) so imperfect heredoc stripping
    like ``cat  gh -R … pr merge`` still classifies the merge verb.
    """
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    for i, tok in enumerate(tokens):
        if tok != "gh":
            continue
        rest = _skip_gh_leading_flags(tokens[i + 1 :])
        if not rest or rest[0] != "pr":
            continue
        j = 1
        while j < len(rest):
            cur = rest[j]
            if cur == "--":
                break
            if cur.startswith("-"):
                j, _repo, _missing = _consume_merge_argv_flag(rest, j)
                continue
            return cur
    return None


def is_gh_pr_merge(part: str) -> bool:
    """True when tokens contain ``gh … pr … merge`` with merge as the subcommand."""
    return _direct_gh_pr_subcommand(part) == "merge"


def _direct_gh_pr_non_merge(part: str) -> bool:
    """True when the segment is a ``gh pr <other>`` (merge only as flag/body data)."""
    sub = _direct_gh_pr_subcommand(part)
    return sub is not None and sub != "merge"


def _command_name_dynamic(tok: str) -> bool:
    """True when a command token may expand to a different executable at runtime."""
    if not tok:
        return False
    # `$…`, backticks, tilde, ANSI-C residue (`$\x67\x68` after shlex).
    if "$" in tok or "`" in tok or tok.startswith("~") or "\\" in tok:
        return True
    # Pathname / brace expansion: `./[g]h`, `gh*`, `?h`, `{-Ra,-Rb}`, …
    if any(c in tok for c in "*?[]{}"):
        return True
    return False


def dynamic_gh_pr_merge(part: str) -> bool:
    """True when ``pr``…``merge`` follows a dynamic executable (not literal ``gh``).

    Example: ``$'\\x67\\x68' -R owner/target pr merge 42`` or ``./[g]h … pr merge``
    runs ``gh`` after Bash expands the name, but tokenizers only see a non-``gh``
    command. Fail closed — do not treat it as unrelated shell input.
    """
    if is_gh_pr_merge(part):
        return False
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    try:
        pr_i = next(i for i, t in enumerate(tokens) if t == "pr")
        next(i for i in range(pr_i + 1, len(tokens)) if tokens[i] == "merge")
    except StopIteration:
        return False
    i = _index_after_env_wrapper(tokens)
    while i < len(tokens) and tokens[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(tokens) or i >= pr_i:
        return False
    cmd = tokens[i]
    if cmd == "gh":
        return False
    return _command_name_dynamic(cmd)


def dynamic_gh_subcommand_merge(part: str) -> bool:
    """True when literal ``gh`` has dynamically expanded ``pr``/``merge`` verbs.

    Example: ``gh "$x" "$y" 42 -R owner/target`` with ``x=pr; y=merge`` — Bash
    runs a real merge, but tokenizers only see ``$x``/``$y``. Fail closed.
    """
    if is_gh_pr_merge(part):
        return False
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    i = _index_after_env_wrapper(tokens)
    while i < len(tokens) and tokens[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(tokens) or tokens[i] != "gh":
        return False
    i += 1
    verbs: list[str] = []
    while i < len(tokens) and len(verbs) < 2:
        tok = tokens[i]
        if tok == "--":
            break
        if tok.startswith("-"):
            next_i, _repo, _missing = _consume_merge_argv_flag(tokens, i)
            i = next_i
            continue
        verbs.append(tok)
        i += 1
    if len(verbs) < 1:
        return False
    a = verbs[0]
    a_dyn = _command_name_dynamic(a)
    # Unquoted ``$x`` may word-split into ``pr merge`` (one token → two verbs).
    # Fail closed on any dynamic first verb after ``gh``.
    if a_dyn:
        return True
    if len(verbs) < 2:
        return False
    b = verbs[1]
    b_dyn = _command_name_dynamic(b)
    # ``gh pr $y`` with y=merge
    return a == "pr" and b_dyn


_MERGE_ASSEMBLY_WORDS = frozenset({"gh", "pr", "merge"})


def _assignment_value_merge_word(val: str) -> str | None:
    """Return ``gh``/``pr``/``merge`` when ``val`` is that literal, else None."""
    plain = _dequote_shell_text(val.strip("'\""))
    if plain in _MERGE_ASSEMBLY_WORDS:
        return plain
    return None


# Simple ``printf`` conversions we can evaluate without shelling out.
_PRINTF_CONV_RE = re.compile(r"%([-+0 #]*)(\d+)?(?:\.(\d+))?([diouxXeEfFgGaAcsb%])")


def _try_bash_printf_format(fmt: str, args: list[str]) -> str | None:
    """Best-effort bash-like ``printf`` for literal formats; None if unsupported."""
    out: list[str] = []
    i = 0
    arg_i = 0
    while i < len(fmt):
        if fmt[i] != "%":
            out.append(fmt[i])
            i += 1
            continue
        m = _PRINTF_CONV_RE.match(fmt, i)
        if not m:
            return None
        conv = m.group(4)
        i = m.end()
        if conv == "%":
            out.append("%")
            continue
        if arg_i >= len(args):
            return None
        arg = args[arg_i]
        arg_i += 1
        if conv == "s":
            out.append(arg)
        elif conv == "c":
            if re.fullmatch(r"-?\d+", arg):
                out.append(chr(int(arg) & 0xFF))
            else:
                out.append(arg[:1] if arg else "\0")
        elif conv in "diouxX":
            try:
                n = int(arg, 0)
            except ValueError:
                return None
            if conv in "diu":
                out.append(str(n))
            elif conv == "o":
                out.append(format(n & 0xFFFFFFFF, "o"))
            elif conv == "x":
                out.append(format(n & 0xFFFFFFFF, "x"))
            else:
                out.append(format(n & 0xFFFFFFFF, "X"))
        else:
            return None
    return "".join(out)


def _merge_words_from_printf_values(tokens: list[str]) -> set[str]:
    """Collect ``gh``/``pr``/``merge`` from ``printf`` format/args (incl. formatting)."""
    found: set[str] = set()
    plain_tokens: list[str] = []
    for tok in tokens:
        if tok.startswith("-") and tok != "-":
            continue
        plain = _dequote_shell_text(tok.strip("'\""))
        plain_tokens.append(plain)
        word = _assignment_value_merge_word(plain)
        if word:
            found.add(word)
    if plain_tokens and not any(_command_name_dynamic(t) for t in plain_tokens):
        rendered = _try_bash_printf_format(plain_tokens[0], plain_tokens[1:])
        if rendered is not None:
            word = _assignment_value_merge_word(rendered)
            if word:
                found.add(word)
            found |= _merge_words_from_text(rendered)
    return found


def _part_has_printf_v(part: str) -> bool:
    """True when ``part`` runs ``printf -v`` / sticky ``-vNAME`` (assigns output)."""
    tokens = _shell_tokens(part)
    rest, _leading = _skip_leading_assignments(tokens)
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(rest):
        return False
    nested = _nested_case_or_arm_body(rest, i)
    if nested is not None:
        return _part_has_printf_v(nested)
    if rest[i] != "printf":
        return False
    for tok in rest[i + 1 :]:
        if tok == "-v":
            return True
        if tok.startswith("-") and tok != "-" and "=" not in tok:
            if tok.startswith("-v") and len(tok) > 2:
                return True
            continue
        break
    return False


def _merge_words_from_text(text: str) -> set[str]:
    """Collect literal ``gh``/``pr``/``merge`` tokens inside free-form text."""
    found: set[str] = set()
    for piece in text.split():
        word = _assignment_value_merge_word(piece)
        if word:
            found.add(word)
    return found


def _merge_words_from_read_redirects(tokens: list[str]) -> set[str]:
    """Collect merge words from ``read`` here-string / heredoc payloads."""
    found: set[str] = set()
    j = 0
    while j < len(tokens):
        tok = tokens[j]
        if tok.startswith("<<<"):
            payload = tok[3:]
            if payload:
                found |= _merge_words_from_text(payload)
            elif j + 1 < len(tokens):
                found |= _merge_words_from_text(tokens[j + 1])
            return found
        if tok == "<<<":
            if j + 1 < len(tokens):
                found |= _merge_words_from_text(tokens[j + 1])
            return found
        if tok.startswith("<<") and not tok.startswith("<<<"):
            raw = tok[2:]
            if raw.startswith("-"):
                raw = raw[1:]
            delim = _dequote_shell_text(raw.strip("'\"")) if raw else None
            start = j + 1
            if not delim and start < len(tokens):
                delim = _dequote_shell_text(tokens[start].strip("'\""))
                start += 1
            body: list[str] = []
            if delim:
                for t in tokens[start:]:
                    if _dequote_shell_text(t.strip("'\"")) == delim:
                        break
                    body.append(t)
            found |= _merge_words_from_text(" ".join(body))
            return found
        j += 1
    return found


def _part_assigns_merge_assembly_words(part: str) -> set[str]:
    """Collect literal ``gh``/``pr``/``merge`` values assigned in ``part``.

    Covers ``NAME=gh``, declaration-style assigns, and builtins that write
    variables such as ``printf -v c gh`` / sticky ``printf -vc gh``, and
    ``read m <<< merge`` / ``read -a a <<< "gh pr merge"``.
    """
    found: set[str] = set()
    tokens = _shell_tokens(part)
    rest, leading = _skip_leading_assignments(tokens)
    for _key, val in leading.items():
        word = _assignment_value_merge_word(val)
        if word:
            found.add(word)
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(rest):
        return found
    nested = _nested_case_or_arm_body(rest, i)
    if nested is not None:
        found |= _part_assigns_merge_assembly_words(nested)
        return found
    head = rest[i]
    m_head = ASSIGNMENT_RE.match(head)
    if m_head:
        word = _assignment_value_merge_word(m_head.group(2))
        if word:
            found.add(word)
        return found
    if head in ("export", "declare", "typeset", "local", "readonly"):
        for tok in rest[i + 1 :]:
            if tok.startswith("-") or tok.startswith("+"):
                continue
            _key, has_eq, val = tok.partition("=")
            if not has_eq:
                continue
            word = _assignment_value_merge_word(val)
            if word:
                found.add(word)
        return found
    # ``printf -v NAME gh`` / ``printf -v NAME %s gh`` / sticky ``-vNAME``.
    if head == "printf":
        j = i + 1
        while j < len(rest):
            tok = rest[j]
            if tok == "-v":
                if j + 1 >= len(rest):
                    break
                found |= _merge_words_from_printf_values(rest[j + 2 :])
                return found
            if tok.startswith("-") and tok != "-" and "=" not in tok:
                if tok.startswith("-v") and len(tok) > 2:
                    found |= _merge_words_from_printf_values(rest[j + 1 :])
                    return found
                j += 1
                continue
            break
        return found
    # ``read m <<< merge`` / ``read -a a <<< "gh pr merge"`` / heredoc bodies.
    if head == "read":
        found |= _merge_words_from_read_redirects(rest[i + 1 :])
    return found


# Plain ``$name`` / ``${name}`` — not a value-transforming expansion.
_SIMPLE_PARAM_EXPANSION = re.compile(
    r"^(?:"
    r"\$[A-Za-z_][A-Za-z0-9_]*"
    r"|\$\{[A-Za-z_][A-Za-z0-9_]*\}"
    r"|\$[0-9]+"
    r"|\$[*@#?\-!]"
    r")$"
)


def _param_expansion_transformed(tok: str) -> bool:
    """True when ``tok`` expands with a transform (``${c:1}``, ``${c#x}``, ``$(…)``)."""
    plain = _dequote_shell_text(tok.strip("'\""))
    if not plain or not _command_name_dynamic(plain):
        return False
    if _SIMPLE_PARAM_EXPANSION.fullmatch(plain):
        return False
    return True


def _part_dynamic_prefix_words(part: str) -> list[str] | None:
    """Return the first three command words when all are dynamic, else None."""
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    i = _index_after_env_wrapper(tokens)
    while i < len(tokens) and tokens[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    words: list[str] = []
    while i < len(tokens) and len(words) < 3:
        tok = tokens[i]
        if tok == "--":
            break
        if tok.startswith("-"):
            # Flags only make sense after the executable; reject mid-prefix.
            if not words:
                return None
            break
        words.append(tok)
        i += 1
    if len(words) != 3 or not all(_command_name_dynamic(w) for w in words):
        return None
    return words


def _part_fully_dynamic_merge_prefix(part: str) -> bool:
    """True when the first three command words are all dynamic (``\"$c\" \"$p\" \"$m\"``)."""
    return _part_dynamic_prefix_words(part) is not None


def _part_transformed_dynamic_merge_prefix(part: str) -> bool:
    """True when a fully dynamic three-word invoke uses parameter transforms.

    ``\"${c:1}\" \"${p:1}\" \"${m:1}\"`` can yield ``gh pr merge`` even when the
    stored values were never exactly those words.
    """
    words = _part_dynamic_prefix_words(part)
    if words is None:
        return False
    return any(_param_expansion_transformed(w) for w in words)


def _apply_concat_assignment(
    concat: dict[str, str], assigned: set[str], tok: str
) -> None:
    """Update ``concat``/``assigned`` for one ``NAME=value`` / ``NAME+=value`` token."""
    m = ASSIGNMENT_RE.match(tok)
    if not m:
        return
    name, val = m.group(1), m.group(2)
    plain = _dequote_shell_text(val.strip("'\""))
    if _assignment_is_append(tok):
        concat[name] = concat.get(name, "") + plain
    else:
        concat[name] = plain
    word = _assignment_value_merge_word(concat[name])
    if word:
        assigned.add(word)


def _part_apply_concat_assignments(
    part: str, concat: dict[str, str], assigned: set[str]
) -> None:
    """Apply ``=`` / ``+=`` assignments in ``part`` onto concat state."""
    tokens = _shell_tokens(part)
    i = 0
    while i < len(tokens) and ASSIGNMENT_RE.match(tokens[i]):
        _apply_concat_assignment(concat, assigned, tokens[i])
        i += 1
    rest = tokens[i:]
    j = 0
    while j < len(rest) and rest[j] in SHELL_PREFIX_KEYWORDS:
        j += 1
    if j >= len(rest):
        return
    nested = _nested_case_or_arm_body(rest, j)
    if nested is not None:
        _part_apply_concat_assignments(nested, concat, assigned)
        return
    head = rest[j]
    if ASSIGNMENT_RE.match(head):
        _apply_concat_assignment(concat, assigned, head)
        return
    if head in ("export", "declare", "typeset", "local", "readonly"):
        for tok in rest[j + 1 :]:
            if tok.startswith("-") or (tok.startswith("+") and "=" not in tok):
                continue
            if ASSIGNMENT_RE.match(tok):
                _apply_concat_assignment(concat, assigned, tok)


def variable_assembled_merge(cmd: str) -> bool:
    """True when ``gh pr merge`` is assembled via variables across segments.

    Example: ``c=gh; p=pr; m=merge; \"$c\" \"$p\" \"$m\" 42 -R owner/repo`` —
    no literal ``gh``/``pr``/``merge`` remain on the invoke line, so
    ``dynamic_gh_pr_merge`` / ``dynamic_gh_subcommand_merge`` miss it.
    Also covers ``printf -v c gh; …``, ``read m <<< merge; …``, append
    stitching such as ``c=g; c+=h; m=mer; m+=ge; …``, transformed expansions
    such as ``\"${c:1}\"``, and formatted ``printf -v c '%sh' g``.
    """
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    if any(is_gh_pr_merge(p) for p in parts):
        return False
    # Fail closed: transforms can yield gh/pr/merge without exact source words.
    if any(_part_transformed_dynamic_merge_prefix(p) for p in parts):
        return True
    # Fail closed: ``printf -v`` can format merge words (``printf -v c '%sh' g``).
    if any(_part_fully_dynamic_merge_prefix(p) for p in parts) and any(
        _part_has_printf_v(p) for p in parts
    ):
        return True
    assigned: set[str] = set()
    concat: dict[str, str] = {}
    for part in parts:
        assigned |= _part_assigns_merge_assembly_words(part)
        _part_apply_concat_assignments(part, concat, assigned)
    if not ({"gh", "pr", "merge"} <= assigned):
        return False
    return any(_part_fully_dynamic_merge_prefix(p) for p in parts)


def dynamic_merge_argv(part: str) -> bool:
    """True when argv after ``merge`` has a dynamic token (may expand to ``-R…``).

    Example: ``gh pr merge 42 "$(printf -- -Rowner/target)"`` — after expansion
    gh treats the token as a repo flag, but the tokenizer never sees a leading
    ``-`` so the gate validates the wrong repository. Fail closed.
    """
    if not is_gh_pr_merge(part):
        return False
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    try:
        gh_i = tokens.index("gh")
        pr_i = next(i for i in range(gh_i + 1, len(tokens)) if tokens[i] == "pr")
        merge_i = next(i for i in range(pr_i + 1, len(tokens)) if tokens[i] == "merge")
    except (ValueError, StopIteration):
        return False
    for tok in tokens[merge_i + 1 :]:
        if tok in {")", "fi", "done", "esac"}:
            continue
        if _command_name_dynamic(tok):
            return True
    return False


def _collapse_empty_quotes(text: str) -> str:
    """Remove adjacent empty quote pairs (``g''h`` → ``gh``)."""
    out = text
    while True:
        nxt = out.replace("''", "").replace('""', "")
        if nxt == out:
            return out
        out = nxt


def _dequote_shell_text(text: str) -> str:
    """Approximate Bash quote-removal for static name matching.

    Strips ``'`` / ``"`` and removes a backslash that escapes the next character
    (``g'h'`` → ``gh``, ``g\\h`` → ``gh``), matching how alias/function names form.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch in ("'", '"'):
            i += 1
            continue
        if ch == "\\" and i + 1 < n:
            out.append(text[i + 1])
            i += 2
            continue
        out.append(ch)
        i += 1
    return "".join(out)


# Interpreters whose ``-c``/``--command`` operand is a nested shell script.
SHELL_INTERPRETERS = frozenset({"bash", "sh", "zsh", "dash", "ksh"})


def _shell_c_payloads(part: str) -> list[str]:
    """Extract ``bash/sh -c`` / ``eval`` script strings from a segment."""
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    payloads: list[str] = []
    i = 0
    while i < len(tokens):
        tok = tokens[i]
        if tok == "eval":
            if i + 1 < len(tokens):
                payloads.append(" ".join(tokens[i + 1 :]))
            break
        name = tok.rsplit("/", 1)[-1]
        if name in SHELL_INTERPRETERS:
            j = i + 1
            while j < len(tokens):
                t = tokens[j]
                if t in ("-c", "--command"):
                    if j + 1 < len(tokens):
                        payloads.append(tokens[j + 1])
                    break
                if t.startswith("--"):
                    j += 1
                    continue
                if t.startswith("-") and t != "-":
                    # ``-lc`` / ``-eu`` clusters — ``c`` takes the next operand.
                    if "c" in t.lstrip("-"):
                        if j + 1 < len(tokens):
                            payloads.append(tokens[j + 1])
                        break
                    j += 1
                    continue
                break
        i += 1
    return payloads


def _extract_command_substitutions(text: str) -> list[str]:
    """Return bodies of ``$(…)``, backtick, ``<(…)``, and ``>(…)`` regions."""
    bodies: list[str] = []
    i = 0
    n = len(text)
    in_single = False
    in_double = False
    while i < n:
        c = text[i]
        if in_single:
            if c == "'":
                in_single = False
            i += 1
            continue
        if in_double:
            if c == "\\" and i + 1 < n:
                i += 2
                continue
            if c == '"':
                in_double = False
                i += 1
                continue
            # Command substitutions still expand inside double quotes.
            if c == "$" and i + 1 < n and text[i + 1] == "(":
                body, nxt = _read_balanced(text, i + 2, "(", ")")
                bodies.append(body)
                bodies.extend(_extract_command_substitutions(body))
                i = nxt
                continue
            if c == "`":
                body, nxt = _read_backtick(text, i + 1)
                bodies.append(body)
                i = nxt
                continue
            i += 1
            continue
        if c == "'":
            in_single = True
            i += 1
            continue
        if c == '"':
            in_double = True
            i += 1
            continue
        if c == "$" and i + 1 < n and text[i + 1] == "(":
            body, nxt = _read_balanced(text, i + 2, "(", ")")
            bodies.append(body)
            bodies.extend(_extract_command_substitutions(body))
            i = nxt
            continue
        if c in "<>" and i + 1 < n and text[i + 1] == "(":
            body, nxt = _read_balanced(text, i + 2, "(", ")")
            bodies.append(body)
            bodies.extend(_extract_command_substitutions(body))
            i = nxt
            continue
        if c == "`":
            body, nxt = _read_backtick(text, i + 1)
            bodies.append(body)
            i = nxt
            continue
        i += 1
    return bodies


def _read_balanced(text: str, start: int, open_ch: str, close_ch: str) -> tuple[str, int]:
    """Read from ``start`` until matching ``close_ch``; return (body, index_after)."""
    depth = 1
    i = start
    n = len(text)
    in_single = False
    in_double = False
    while i < n:
        c = text[i]
        if in_single:
            if c == "'":
                in_single = False
            i += 1
            continue
        if in_double:
            if c == "\\" and i + 1 < n:
                i += 2
                continue
            if c == '"':
                in_double = False
            i += 1
            continue
        if c == "'":
            in_single = True
            i += 1
            continue
        if c == '"':
            in_double = True
            i += 1
            continue
        if c == open_ch:
            depth += 1
        elif c == close_ch:
            depth -= 1
            if depth == 0:
                return text[start:i], i + 1
        i += 1
    return text[start:], n


def _read_backtick(text: str, start: int) -> tuple[str, int]:
    i = start
    n = len(text)
    while i < n:
        if text[i] == "\\" and i + 1 < n:
            i += 2
            continue
        if text[i] == "`":
            return text[start:i], i + 1
        i += 1
    return text[start:], n


def nested_merge_in_segment(part: str) -> bool:
    """True when ``$(gh … pr merge)`` / backticks nest inside the segment.

    Covers ``X=\"$(gh -R target pr merge 2)\" gh -R safe pr merge 1`` where the
    outer tokens look like a direct merge so the shell-wrapped predicate skips.
    """
    for body in _extract_command_substitutions(part):
        if MERGE_RE.search(body) or is_gh_pr_merge(body):
            return True
        if dynamic_gh_pr_merge(body) or quote_smashed_merge(body):
            return True
    return False


def opaque_shell_wrapper_pr_merge(part: str) -> bool:
    """True when a shell ``-c``/eval payload hides a dynamic ``pr``…``merge``.

    Example: ``bash -c 'x=g; x+=h; \"$x\" -R owner/target pr merge 2'`` — Bash
    runs ``gh``, but the outer tokenizer never sees ``gh`` / ``MERGE_RE``. Inspect
    nested script segments with the same dynamic-merge detectors.
    """
    for payload in _shell_c_payloads(part):
        subparts = [p for p, _ in split_shell_chains(payload)] or [payload]
        if any(dynamic_gh_pr_merge(p) for p in subparts):
            return True
        if any(dynamic_gh_subcommand_merge(p) for p in subparts):
            return True
        if quote_smashed_merge(payload) or any(quote_smashed_merge(p) for p in subparts):
            return True
        # Nested quote-smashed / escaped ``gh`` that only appears after dequote.
        norm = _dequote_shell_text(payload)
        if norm != payload:
            norm_parts = [p for p, _ in split_shell_chains(norm)] or [norm]
            if MERGE_RE.search(norm) or any(dynamic_gh_pr_merge(p) for p in norm_parts):
                return True
    return False


def quote_smashed_merge(cmd: str) -> bool:
    """True when quote-concatenation hides ``gh`` before ``pr``…``merge``.

    Example: ``bash -c 'g''h -R owner/target pr merge 42'`` — Bash concatenates
    ``g''h`` into ``gh``, but ``MERGE_RE`` / ``shlex`` never see a ``gh`` token.
    """
    if MERGE_RE.search(cmd):
        return False
    collapsed = _collapse_empty_quotes(cmd)
    if collapsed != cmd and MERGE_RE.search(collapsed):
        return True
    if QUOTE_SMASHED_GH_RE.search(cmd) and re.search(
        r"(?<![\w-])pr(?![\w-]).*(?<![\w-])merge(?![\w-])", cmd, re.S | re.I
    ):
        return True
    return False


_ARRAY_ASSIGN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\+?=\(")
_ARRAY_EXPAND_TOKEN_RE = re.compile(r"^\$\{[A-Za-z_][A-Za-z0-9_]*\[(@|\*)\]\}$")
_PR_MERGE_LOOSE_RE = re.compile(r"(?<![\w-])pr(?![\w-]).*(?<![\w-])merge(?![\w-])", re.S | re.I)


def _part_array_assign_has_merge(part: str) -> bool:
    """True when ``name=(…)`` / ``name+=(…)`` argv looks like a ``gh pr merge``."""
    if not _ARRAY_ASSIGN_RE.search(part):
        return False
    for candidate in (part, _dequote_shell_text(part)):
        if MERGE_RE.search(candidate) or _PR_MERGE_LOOSE_RE.search(candidate):
            return True
    return False


def _part_is_array_expand_command(part: str) -> bool:
    """True when the executed command is ``${a[@]}`` / ``${a[*]}`` (array expand)."""
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    i = 0
    while i < len(tokens) and tokens[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(tokens):
        return False
    return bool(_ARRAY_EXPAND_TOKEN_RE.match(tokens[i]))


def array_assembled_merge(cmd: str) -> bool:
    """True when a Bash array is built with merge argv or expanded as a command.

    Example: ``a=(g\\h -R owner/target pr merge 2); \"${a[@]}\"`` — quote removal
    makes element 0 ``gh``, and the expand runs an unchecked merge while neither
    segment matches ``is_gh_pr_merge``.
    """
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    if any(_part_array_assign_has_merge(p) for p in parts):
        return True
    if any(_part_is_array_expand_command(p) for p in parts) and (
        MERGE_RE.search(cmd)
        or _PR_MERGE_LOOSE_RE.search(cmd)
        or _PR_MERGE_LOOSE_RE.search(_dequote_shell_text(cmd))
    ):
        return True
    return False


_POSITIONAL_EXPAND_TOKEN_RE = re.compile(
    r"^\$?\{?(@|\*|[0-9]+)\}?$"
)


def _part_set_positional_args(part: str) -> list[str] | None:
    """Return argv after ``set --`` / ``set`` positionals, or None if not a set."""
    tokens = _shell_tokens(part)
    rest, _leading = _skip_leading_assignments(tokens)
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(rest) or rest[i] != "set":
        return None
    j = i + 1
    while j < len(rest):
        tok = rest[j]
        if tok == "--":
            return rest[j + 1 :]
        if tok in ("-o", "+o"):
            j += 2
            continue
        if tok.startswith("-") or tok.startswith("+"):
            j += 1
            continue
        # ``set arg1 arg2`` without ``--`` replaces positionals.
        return rest[j:]
    return []


def _part_set_positionals_has_merge_bits(part: str) -> bool:
    """True when ``set`` positionals mention ``gh`` / ``pr`` / ``merge`` fragments."""
    args = _part_set_positional_args(part)
    if not args:
        return False
    joined = " ".join(args)
    for candidate in (joined, _dequote_shell_text(joined)):
        if MERGE_RE.search(candidate) or _PR_MERGE_LOOSE_RE.search(candidate):
            return True
    interesting = {"gh", "pr", "merge", "$@", "$*", "${@}", "${*}"}
    return any(a in interesting for a in args)


def _part_is_positional_expand_command(part: str) -> bool:
    """True when the executed command is ``\"$@\"`` / ``$*`` / ``$1`` / …."""
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    i = 0
    while i < len(tokens) and tokens[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(tokens):
        return False
    tok = tokens[i]
    if tok in ("$@", "$*", "${@}", "${*}"):
        return True
    return bool(_POSITIONAL_EXPAND_TOKEN_RE.match(tok)) and (
        "@" in tok or "*" in tok or tok.lstrip("$").strip("{}").isdigit()
    )


def positional_assembled_merge(cmd: str) -> bool:
    """True when positional parameters assemble a merge across segments.

    Example: ``set -- gh -R owner/target pr; set -- \"$@\" merge 2; \"$@\"`` —
    no single segment matches ``is_gh_pr_merge``, but Bash runs the merge.
    """
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    has_set_bits = any(_part_set_positionals_has_merge_bits(p) for p in parts)
    has_expand = any(_part_is_positional_expand_command(p) for p in parts)
    if has_set_bits and has_expand:
        return True
    # ``set -- gh … pr merge …`` alone (complete merge in positionals).
    for part in parts:
        args = _part_set_positional_args(part)
        if not args:
            continue
        joined = " ".join(args)
        for candidate in (joined, _dequote_shell_text(joined)):
            if MERGE_RE.search(candidate) or _PR_MERGE_LOOSE_RE.search(candidate):
                return True
    if has_expand and (
        MERGE_RE.search(cmd)
        or _PR_MERGE_LOOSE_RE.search(cmd)
        or _PR_MERGE_LOOSE_RE.search(_dequote_shell_text(cmd))
    ):
        return True
    return False


# First-level ``gh`` commands from ``gh help`` (incl. preview builtins).
# Unknown words may be aliases that expand to ``pr merge``.
GH_TOP_LEVEL_COMMANDS = frozenset(
    {
        "agent-task",
        "alias",
        "api",
        "attestation",
        "auth",
        "browse",
        "cache",
        "co",
        "codespace",
        "completion",
        "config",
        "copilot",
        "discussion",
        "extension",
        "gist",
        "gpg-key",
        "help",
        "issue",
        "label",
        "licenses",
        "org",
        "pr",
        "preview",
        "project",
        "release",
        "repo",
        "ruleset",
        "run",
        "search",
        "secret",
        "skill",
        "ssh-key",
        "status",
        "variable",
        "version",
        "workflow",
    }
)
# ``gh pr`` subcommands from ``gh pr --help`` — anything else after ``pr`` may be
# a multiword alias (``gh alias set 'pr sneak' 'pr merge …'`` → ``gh pr sneak``).
GH_PR_SUBCOMMANDS = frozenset(
    {
        "checkout",
        "checks",
        "close",
        "comment",
        "create",
        "diff",
        "edit",
        "list",
        "lock",
        "merge",
        "ready",
        "reopen",
        "revert",
        "review",
        "status",
        "unlock",
        "update-branch",
        "view",
    }
)
# Known subcommands per top-level (from ``gh <cmd> --help``). Namespaces that
# take freeform args (``api``, ``browse``, …) are omitted — second words there
# are not treated as multiword-alias probes.
GH_SUBCOMMANDS_BY_TOP: dict[str, frozenset[str]] = {
    "agent-task": frozenset({"create", "list", "view"}),
    "alias": frozenset({"delete", "import", "list", "set"}),
    "attestation": frozenset({"download", "trusted-root", "verify"}),
    "auth": frozenset(
        {"login", "logout", "refresh", "setup-git", "status", "switch", "token"}
    ),
    "cache": frozenset({"delete", "list"}),
    "codespace": frozenset(
        {
            "code",
            "cp",
            "create",
            "delete",
            "edit",
            "jupyter",
            "list",
            "logs",
            "ports",
            "rebuild",
            "ssh",
            "stop",
            "view",
        }
    ),
    "config": frozenset({"clear-cache", "get", "list", "set"}),
    "discussion": frozenset({"comment", "create", "edit", "list", "view"}),
    "extension": frozenset(
        {
            "browse",
            "create",
            "exec",
            "install",
            "list",
            "remove",
            "search",
            "upgrade",
        }
    ),
    "gist": frozenset(
        {"clone", "create", "delete", "edit", "list", "rename", "view"}
    ),
    "gpg-key": frozenset({"add", "delete", "list"}),
    "issue": frozenset(
        {
            "artifact",
            "close",
            "comment",
            "create",
            "delete",
            "develop",
            "edit",
            "list",
            "lock",
            "pin",
            "reopen",
            "status",
            "transfer",
            "unlock",
            "unpin",
            "view",
        }
    ),
    "label": frozenset({"clone", "create", "delete", "edit", "list"}),
    "org": frozenset({"list"}),
    "pr": GH_PR_SUBCOMMANDS,
    "project": frozenset(
        {
            "close",
            "copy",
            "create",
            "delete",
            "edit",
            "field-create",
            "field-delete",
            "field-list",
            "item-add",
            "item-archive",
            "item-create",
            "item-delete",
            "item-edit",
            "item-list",
            "link",
            "list",
            "mark-template",
            "unlink",
            "view",
        }
    ),
    "release": frozenset(
        {
            "create",
            "delete",
            "delete-asset",
            "download",
            "edit",
            "list",
            "upload",
            "verify",
            "verify-asset",
            "view",
        }
    ),
    "repo": frozenset(
        {
            "archive",
            "autolink",
            "clone",
            "create",
            "delete",
            "deploy-key",
            "edit",
            "fork",
            "gitignore",
            "license",
            "list",
            "read-dir",
            "read-file",
            "rename",
            "set-default",
            "sync",
            "unarchive",
            "view",
        }
    ),
    "ruleset": frozenset({"check", "list", "view"}),
    "run": frozenset(
        {"cancel", "delete", "download", "list", "rerun", "view", "watch"}
    ),
    "search": frozenset({"code", "commits", "issues", "prs", "repos"}),
    "secret": frozenset({"delete", "list", "set"}),
    "skill": frozenset(
        {"install", "list", "preview", "publish", "search", "update"}
    ),
    "ssh-key": frozenset({"add", "delete", "list"}),
    "variable": frozenset({"delete", "get", "list", "set"}),
    "workflow": frozenset({"disable", "enable", "list", "run", "view"}),
}
# Third-level allowlists for ``gh <top> <sub> <nested>`` (from ``gh … --help``).
# Unknown third words under these paths may be multiword aliases
# (``gh alias set 'repo autolink sneak' 'pr merge …'`` → ``gh repo autolink sneak``).
GH_NESTED_SUBCOMMANDS: dict[tuple[str, str], frozenset[str]] = {
    ("codespace", "ports"): frozenset({"forward", "visibility"}),
    ("issue", "artifact"): frozenset(
        {"create", "delete", "download", "edit", "list", "view"}
    ),
    ("repo", "autolink"): frozenset({"create", "delete", "list", "view"}),
    ("repo", "deploy-key"): frozenset({"add", "delete", "list"}),
    ("repo", "gitignore"): frozenset({"list", "view"}),
    ("repo", "license"): frozenset({"list", "view"}),
}
GH_ALIAS_MUTATE = frozenset({"set", "import", "delete"})
GH_GLOBAL_VALUE_FLAGS = frozenset({"-R", "--repo", "--hostname"})


def _tokens_after_gh(part: str) -> list[str] | None:
    """Return tokens following a direct ``gh`` (optional env/keywords), or None."""
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    i = _index_after_env_wrapper(tokens)
    while i < len(tokens) and tokens[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(tokens) or tokens[i] != "gh":
        return None
    return tokens[i + 1 :]


def _skip_gh_leading_flags(tokens: list[str]) -> list[str]:
    """Consume global ``gh`` flags (``-R``/``--repo``/``--hostname``) before the command."""
    i = 0
    n = len(tokens)
    while i < n:
        tok = tokens[i]
        if tok == "--":
            return tokens[i + 1 :]
        if tok in GH_GLOBAL_VALUE_FLAGS:
            i += 2
            continue
        if tok.startswith("--repo=") or tok.startswith("--hostname="):
            i += 1
            continue
        if tok.startswith("-R") and tok != "-R":
            i += 1
            continue
        if tok in ("--help", "--version"):
            i += 1
            continue
        break
    return tokens[i:]


def _part_gh_alias_configures(part: str) -> bool:
    """True when the segment runs ``gh alias set|import|delete``."""
    rest = _tokens_after_gh(part)
    if rest is None:
        return False
    rest = _skip_gh_leading_flags(rest)
    if not rest or rest[0] != "alias":
        return False
    for tok in rest[1:]:
        if tok.startswith("-"):
            continue
        return tok in GH_ALIAS_MUTATE
    return False


def _part_opaque_gh_command(part: str) -> bool:
    """True when ``gh`` invokes a possible alias rather than a known command path.

    Covers ``gh sneak``, ``gh -R owner/repo sneak``, multiword aliases under
    any namespaced command (``gh pr sneak``, ``gh repo sneak``), and aliases
    nested below a known second-level path (``gh repo autolink sneak`` after
    ``gh alias set 'repo autolink sneak' 'pr merge …'``).
    """
    rest = _tokens_after_gh(part)
    if rest is None:
        return False
    rest = _skip_gh_leading_flags(rest)
    if not rest:
        return False
    sub = rest[0]
    if sub.startswith("-"):
        return False
    if sub not in GH_TOP_LEVEL_COMMANDS:
        return True
    # Multiword alias under a known namespace: skip flags, then require a known
    # subcommand when we have an allowlist for that top-level command.
    after = _skip_gh_leading_flags(rest[1:])
    if not after:
        return False
    nxt = after[0]
    if nxt.startswith("-"):
        return False
    known = GH_SUBCOMMANDS_BY_TOP.get(sub)
    if known is None:
        # Freeform tops (``api``, ``browse``, …) — second word is an argument.
        return False
    if nxt not in known:
        return True
    # Nested third-level path: ``gh repo autolink <cmd>`` — unknown third words
    # may be multiword aliases under that nested namespace.
    nested = GH_NESTED_SUBCOMMANDS.get((sub, nxt))
    if nested is None:
        return False
    deeper = _skip_gh_leading_flags(after[1:])
    if not deeper:
        return False
    leaf = deeper[0]
    if leaf.startswith("-"):
        return False
    return leaf not in nested


def gh_alias_merge_risk(cmd: str) -> bool:
    """True when a ``gh`` alias may be configured or invoked instead of ``pr merge``.

    ``gh alias set sneak 'pr merge 2 -R owner/target'; gh sneak`` never matches
    ``is_gh_pr_merge``, so the gate would otherwise allow it. Fail closed on alias
    mutation and on opaque ``gh <name>`` / ``gh <ns> <alias>`` /
    ``gh <ns> <sub> <alias>`` invocations.
    """
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    return any(
        _part_gh_alias_configures(p) or _part_opaque_gh_command(p) for p in parts
    )


def env_wraps_merge(part: str) -> bool:
    """True when `env` appears before `gh` in the segment (any -C/--chdir spelling)."""
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    try:
        gh_i = next(i for i, t in enumerate(tokens) if t == "gh")
    except StopIteration:
        return False
    return any(t == "env" for t in tokens[:gh_i])


def _index_after_env_wrapper(tokens: list[str]) -> int:
    """Return index of the command after an optional leading ``env`` wrapper."""
    if not tokens or tokens[0] != "env":
        return 0
    i = 1
    while i < len(tokens):
        tok = tokens[i]
        if ASSIGNMENT_RE.match(tok):
            i += 1
            continue
        if tok.startswith("-"):
            if tok in ("-", "-i", "--ignore-environment"):
                i += 1
                continue
            if tok.startswith("--") and "=" in tok:
                i += 1
                continue
            if tok.startswith("-u") and tok != "-u":
                i += 1
                continue
            if tok.startswith("-C") and tok != "-C":
                i += 1
                continue
            base = tok.split("=", 1)[0]
            if base in ENV_VALUE_FLAGS:
                i += 2
                continue
            i += 1
            continue
        break
    return i


# Shell words that may precede a local ``gh`` / builtin (control flow / wrappers).
# Includes ``if``/``while``/``until`` so ``if getopts …`` / ``while getopts …``
# still reach the getopts/PATH scanners (``for``/``select`` stay heads, not prefixes).
# Brace-group ``{`` keeps assignments in the current shell (``{ PATH=/tmp; }; gh …``);
# split segments often start with ``{`` alone, so strip it like other prefixes.
SHELL_PREFIX_KEYWORDS = frozenset(
    {
        "if",
        "while",
        "until",
        "then",
        "do",
        "else",
        "elif",
        "{",
        "time",
        "command",
        "builtin",
        "exec",
        "!",
    }
)


def gh_is_direct_command(part: str) -> bool:
    """True when ``gh`` is the executed binary (optional ``env`` / shell keywords).

    Rejects ``ssh``/``xargs``/``docker``/… wrappers that run merge in another
    environment or append unseen argv — fail closed; require a direct ``gh``.
    """
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    i = _index_after_env_wrapper(tokens)
    while i < len(tokens) and tokens[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    return i < len(tokens) and tokens[i] == "gh"


def scoped_dir_requires_repo(part: str) -> bool:
    """True when the segment uses env/subshell chdir we refuse to model without -R."""
    return env_wraps_merge(part) or bool(SUBSHELL_CD_RE.search(part))


# Git location / config overrides change which repo `gh` sees without `-R`.
GIT_LOCATION_VARS = frozenset({"GIT_DIR", "GIT_WORK_TREE", "GIT_COMMON_DIR"})
GIT_CONFIG_VARS = frozenset(
    {
        "GIT_CONFIG",
        "GIT_CONFIG_GLOBAL",
        "GIT_CONFIG_SYSTEM",
        "GIT_CONFIG_NOSYSTEM",
        "GIT_CONFIG_COUNT",
    }
)


def is_git_env_override_key(key: str) -> bool:
    """True for GIT_DIR / GIT_CONFIG_COUNT / GIT_CONFIG_KEY_n / … overrides."""
    if key in GIT_LOCATION_VARS or key in GIT_CONFIG_VARS:
        return True
    return key.startswith("GIT_CONFIG_KEY_") or key.startswith("GIT_CONFIG_VALUE_")


def sets_git_location(part: str) -> bool:
    """True when the command sets GIT_DIR / GIT_WORK_TREE / GIT_CONFIG_* overrides."""
    tokens = _shell_tokens(part)
    rest, leading = _skip_leading_assignments(tokens)
    if any(is_git_env_override_key(k) for k in leading):
        return True
    env_assigns, _cleared = _env_wrapper_state(rest)
    return any(is_git_env_override_key(k) for k in env_assigns)


def _is_path_name(name: str) -> bool:
    """True when ``name`` is PATH or an indexed PATH assignment target."""
    return _env_key_base(name) == "PATH"


def _var_target_dynamic(name: str) -> bool:
    """True when a var/hash name operand may expand at runtime.

    Covers ``$v`` / ``${v}`` and brace/glob forms such as ``g{h,h}`` that Bash
    expands before builtins like ``hash -p`` / ``printf -v`` see the name.
    """
    return _command_name_dynamic(name)


def _body_after_pattern_closer(tok: str, rest: list[str], closer_i: int) -> str | None:
    """Return command text after a ``pat)`` / ``)`` token at ``closer_i``."""
    after_sticky = ""
    if tok.endswith(")") and tok != ")":
        after_sticky = tok.split(")", 1)[1]
    body_toks: list[str] = []
    if after_sticky:
        body_toks.append(after_sticky)
    body_toks.extend(rest[closer_i + 1 :])
    body = " ".join(body_toks).strip()
    return body or None


def _case_arm_body(rest: list[str], case_i: int) -> str | None:
    """Return the command text after the first ``case`` pattern closer ``)``.

    ``case x in x) PATH=/tmp/fake`` tokenizes with a leading ``case`` head, so
    ordinary leading-assignment scans miss the arm body.
    """
    j = case_i + 1
    while j < len(rest) and not (
        rest[j].endswith(")") and rest[j] not in (")", "((")
    ):
        # Bare ``)`` also closes a pattern; sticky ``x)PATH=…`` is handled below.
        if rest[j] == ")":
            break
        j += 1
    if j >= len(rest):
        return None
    return _body_after_pattern_closer(rest[j], rest, j)


def _pattern_arm_body(rest: list[str], i: int) -> str | None:
    """Return body after a standalone ``pat)`` segment (later arms after ``;;``).

    ``split_shell_chains`` turns ``…;; x) PATH=/tmp/fake;;`` into the segment
    ``x) PATH=/tmp/fake``, which has no leading ``case`` keyword.
    """
    if i >= len(rest):
        return None
    tok = rest[i]
    if tok == ")":
        return _body_after_pattern_closer(tok, rest, i)
    if not tok.endswith(")") or tok in ("((",):
        return None
    # ``gh()`` / ``name()`` function heads put ``(`` mid-token; case patterns
    # are ``x)`` / ``*)`` or the optional ``(x)`` form.
    if "(" in tok and not tok.startswith("("):
        return None
    return _body_after_pattern_closer(tok, rest, i)


def _nested_case_or_arm_body(rest: list[str], i: int) -> str | None:
    """Nested body for ``case …)`` heads or standalone ``pat)`` arm segments."""
    if i >= len(rest):
        return None
    if rest[i] == "case":
        return _case_arm_body(rest, i)
    return _pattern_arm_body(rest, i)


def _arith_assignment_targets(part: str) -> list[str]:
    """Return name operands assigned by ``((…))`` / ``let`` in ``part``.

    Covers sticky ``((PATH=0))``, spaced ``(( PATH = 0 ))``, and ``let PATH=0``.
    """
    tokens = _shell_tokens(part)
    rest, _leading = _skip_leading_assignments(tokens)
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(rest):
        return []
    head = rest[i]
    names: list[str] = []
    if head == "let":
        args = rest[i + 1 :]
        j = 0
        while j < len(args):
            tok = args[j]
            key, has_eq, _val = tok.partition("=")
            if has_eq and key:
                names.append(key)
                j += 1
                continue
            if j + 1 < len(args) and args[j + 1] == "=":
                names.append(tok)
                j += 2
                continue
            if j + 1 < len(args) and args[j + 1].startswith("="):
                names.append(tok)
                j += 2
                continue
            j += 1
        return names
    if head.startswith("(("):
        blob = " ".join(rest[i:])
        # Strip outer ``((`` / ``))`` when present; keep inner text for scans.
        inner = blob
        if inner.startswith("(("):
            inner = inner[2:]
        if inner.endswith("))"):
            inner = inner[:-2]
        for m in re.finditer(r"(?<![\w.])([A-Za-z_][\w.]*)\s*=", inner):
            names.append(m.group(1))
        # Dynamic tokens inside the arithmetic expression.
        for tok in rest[i:]:
            if _var_target_dynamic(tok):
                names.append(tok)
        return names
    return []


def sets_path_override(part: str) -> bool:
    """True when the segment assigns/clears PATH (can swap which ``gh`` runs).

    Includes indexed writes such as ``PATH[0]=/tmp/fake`` (Bash converts the
    exported scalar into an array used for command lookup), loop targets
    (``for PATH in …`` / ``select PATH in …``), ``case`` arm bodies
    (``case x in x) PATH=…``), ``getopts`` name targets, arithmetic / ``let``
    assignments (``((PATH=0))``), shell-level ``unset PATH`` (literal or
    dynamic), and dynamic writers such as ``printf -v \"$v\" …`` where ``$v``
    may expand to ``PATH``.
    """
    if any(
        _is_path_name(n) or _var_target_dynamic(n)
        for n in _arith_assignment_targets(part)
    ):
        return True
    tokens = _shell_tokens(part)
    rest, leading = _skip_leading_assignments(tokens)
    if any(_is_path_name(k) for k in leading):
        return True
    # Bare ``PATH[0]=…`` segment when ASSIGNMENT_RE matched into leading above;
    # also catch when the whole segment is a single indexed assignment token.
    if not rest and any(_is_path_name(k) for k in leading):
        return True
    env_assigns, cleared = _env_wrapper_state(rest)
    if any(_is_path_name(k) for k in env_assigns) or any(
        _is_path_name(k) for k in cleared
    ):
        return True
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(rest):
        # Segment is only assignments (e.g. ``PATH[0]=/tmp/fake`` alone).
        return any(_is_path_name(k) for k in leading)
    head = rest[i]
    # ``case …)`` / standalone ``pat) PATH=…`` (later arms after ``;;``).
    nested = _nested_case_or_arm_body(rest, i)
    if nested is not None:
        return sets_path_override(nested)
    # Standalone indexed assignment mistaken as the command token.
    # Also ``if PATH=/tmp/fake`` after control-flow prefix skip.
    m_head = ASSIGNMENT_RE.match(head)
    if m_head and _is_path_name(m_head.group(1)):
        return True
    # ``export PATH=…`` / ``declare PATH=…`` / ``typeset`` / ``local`` / ``readonly``
    if head in ("export", "declare", "typeset", "local", "readonly"):
        for tok in rest[i + 1 :]:
            if tok.startswith("-") or tok.startswith("+"):
                continue
            key, _, _val = tok.partition("=")
            if _is_path_name(key) or _var_target_dynamic(key):
                return True
        return False
    # ``printf -v PATH …`` / ``printf -v "$v" …`` / sticky ``-vPATH``
    if head == "printf":
        j = i + 1
        while j < len(rest):
            tok = rest[j]
            if tok in ("-v",):
                if j + 1 < len(rest) and (
                    _is_path_name(rest[j + 1]) or _var_target_dynamic(rest[j + 1])
                ):
                    return True
                j += 2
                continue
            if tok.startswith("-") and tok != "-" and "=" not in tok:
                # sticky ``-vPATH`` / ``-vPATH[0]`` etc.
                if "v" in tok[1:] and _is_path_name(tok.lstrip("-").lstrip("v")):
                    return True
                if "v" in tok[1:] and tok.endswith("PATH") and len(tok) > 2:
                    return True
                j += 1
                continue
            break
        return False
    # ``read PATH`` / ``read "$v"`` / ``mapfile`` / ``readarray``
    if head in ("read", "mapfile", "readarray"):
        for tok in rest[i + 1 :]:
            if tok.startswith("-"):
                continue
            if _is_path_name(tok) or _var_target_dynamic(tok):
                return True
        return False
    # ``for PATH in …`` / ``select PATH in …`` assign each element to NAME while
    # keeping an inherited export — same class as ``PATH=…`` before a merge.
    if head in ("for", "select"):
        if i + 1 < len(rest) and (
            _is_path_name(rest[i + 1]) or _var_target_dynamic(rest[i + 1])
        ):
            return True
        return False
    # ``getopts optstring NAME [args]`` writes the next option letter into NAME.
    if head == "getopts":
        if i + 2 < len(rest) and (
            _is_path_name(rest[i + 2]) or _var_target_dynamic(rest[i + 2])
        ):
            return True
        return False
    # ``unset PATH`` / ``unset "$v"`` clears PATH for later merge children
    # (e.g. ``unset PATH; : ${PATH:=/tmp/fake}; gh …``).
    if head == "unset":
        for tok in rest[i + 1 :]:
            if tok.startswith("-"):
                continue
            if _is_path_name(tok) or _var_target_dynamic(tok):
                return True
        return False
    return False


def path_override_for_merge(cmd: str) -> bool:
    """True when a merge command may run under a command-scoped PATH override."""
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    if not any(is_gh_pr_merge(p) for p in parts):
        return False
    return any(sets_path_override(p) for p in parts)


def _is_tracked_gh_name(name: str) -> bool:
    """True when ``name`` is a tracked gh/config var (optionally indexed)."""
    return _env_key_base(name) in GH_TRACKED_ENV_VARS


def _part_exports_tracked_gh(part: str) -> bool:
    """True when the segment mutates a tracked gh/config env var for later children.

    Covers ``export``, ``declare``/``readonly``, standalone ``GH_HOST=…``,
    indirect writers (``printf -v``, ``read``, ``mapfile``/``readarray``,
    ``getopts``), arithmetic / ``let`` assignments, and shell-loop targets
    (``for GH_HOST in …`` / ``select GH_HOST in …``). Bash keeps the export
    attribute on reassignment, so an inherited exported value is updated for
    the merge child only.
    """
    if any(
        _is_tracked_gh_name(n) or _var_target_dynamic(n)
        for n in _arith_assignment_targets(part)
    ):
        return True
    tokens = _shell_tokens(part)
    rest, leading = _skip_leading_assignments(tokens)
    # Bare ``NAME=value`` segment with no command — persists in the shell.
    if any(_is_tracked_gh_name(k) for k in leading) and not rest:
        return True
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(rest):
        return False
    head = rest[i]
    # ``case …)`` / standalone ``pat) GH_HOST=…`` (later arms after ``;;``).
    nested = _nested_case_or_arm_body(rest, i)
    if nested is not None:
        return _part_exports_tracked_gh(nested)
    # ``if GH_HOST=…`` after control-flow prefix skip — keeps export attribute.
    m_head = ASSIGNMENT_RE.match(head)
    if m_head and _is_tracked_gh_name(m_head.group(1)):
        return True
    if head == "export":
        for tok in rest[i + 1 :]:
            if tok.startswith("-") and "=" not in tok:
                continue
            key = tok.split("=", 1)[0]
            if _is_tracked_gh_name(key):
                return True
        return False
    if head in ("declare", "typeset", "local", "readonly"):
        # ``declare``/``readonly GH_HOST=…`` keeps an inherited export attribute;
        # ``declare -x`` also marks new exports. Either form mutates the merge child.
        for tok in rest[i + 1 :]:
            if tok.startswith("-") or tok.startswith("+"):
                continue
            key, has_assign, _val = tok.partition("=")
            if has_assign and _is_tracked_gh_name(key):
                return True
        return False
    # ``for GH_HOST in …`` / ``select GH_HOST in …`` assign each element to NAME.
    if head in ("for", "select"):
        if i + 1 < len(rest) and _is_tracked_gh_name(rest[i + 1]):
            return True
        return False
    # ``printf -v GH_HOST …`` / ``printf -v "$v" …`` / sticky ``-vGH_HOST``
    if head == "printf":
        j = i + 1
        while j < len(rest):
            tok = rest[j]
            if tok in ("-v",):
                if j + 1 < len(rest) and (
                    _is_tracked_gh_name(rest[j + 1])
                    or _var_target_dynamic(rest[j + 1])
                ):
                    return True
                j += 2
                continue
            if tok.startswith("-") and tok != "-" and "=" not in tok:
                if "v" in tok[1:]:
                    sticky = tok.lstrip("-").lstrip("v")
                    if sticky and _is_tracked_gh_name(sticky):
                        return True
                j += 1
                continue
            break
        return False
    # ``read GH_HOST`` / ``read "$v"`` / ``mapfile`` / ``readarray``
    if head in ("read", "mapfile", "readarray"):
        for tok in rest[i + 1 :]:
            if tok.startswith("-"):
                continue
            if _is_tracked_gh_name(tok) or _var_target_dynamic(tok):
                return True
        return False
    # ``getopts optstring NAME [args]`` writes into NAME (keeps export attr).
    if head == "getopts":
        if i + 2 < len(rest) and (
            _is_tracked_gh_name(rest[i + 2]) or _var_target_dynamic(rest[i + 2])
        ):
            return True
        return False
    return False


def prior_tracked_gh_export(cmd: str) -> bool:
    """True when an earlier segment mutates GH_HOST/config before a merge.

    ``export`` / ``declare -x`` / standalone ``GH_HOST=…`` persist across
    ``;``/``&&`` while ``check_one`` only sees the merge segment — fail closed
    rather than validating the wrong host.
    """
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    seen_export = False
    for part in parts:
        if is_gh_pr_merge(part):
            if seen_export:
                return True
            continue
        if _part_exports_tracked_gh(part):
            seen_export = True
    return False


def _part_unsets_tracked_gh(part: str) -> bool:
    """True when the segment drops a tracked gh/config var from the child env.

    Covers ``unset NAME``, ``export -n NAME``, and ``declare``/``typeset``/
    ``local +x NAME`` (removes the export attribute so the merge child no longer
    inherits an exported hook-process value).
    """
    tokens = _shell_tokens(part)
    rest, _leading = _skip_leading_assignments(tokens)
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(rest):
        return False
    head = rest[i]
    # ``case …)`` / standalone ``pat) unset GH_HOST`` (later arms after ``;;``).
    nested = _nested_case_or_arm_body(rest, i)
    if nested is not None:
        return _part_unsets_tracked_gh(nested)
    if head == "unset":
        for tok in rest[i + 1 :]:
            if tok.startswith("-"):
                continue
            # ``unset 'GH_HOST[0]'`` removes the scalar the same as ``unset GH_HOST``.
            # ``unset "$v"`` may expand to a tracked name at runtime.
            if _is_tracked_gh_name(tok) or _var_target_dynamic(tok):
                return True
        return False
    if head == "export":
        # ``export -n GH_HOST`` removes the export attribute.
        drop_export = False
        for tok in rest[i + 1 :]:
            if tok.startswith("-") and "=" not in tok:
                if "n" in tok[1:]:
                    drop_export = True
                continue
            key = tok.split("=", 1)[0]
            if drop_export and (
                _is_tracked_gh_name(key) or _var_target_dynamic(key)
            ):
                return True
        return False
    if head not in ("declare", "typeset", "local"):
        return False
    # ``declare +x GH_HOST`` / ``typeset +x GH_HOST``
    unexport_mark = False
    for tok in rest[i + 1 :]:
        if tok.startswith("+") and "=" not in tok:
            if "x" in tok[1:]:
                unexport_mark = True
            continue
        if tok.startswith("-"):
            continue
        key = tok.split("=", 1)[0]
        if unexport_mark and (
            _is_tracked_gh_name(key) or _var_target_dynamic(key)
        ):
            return True
    return False


def prior_tracked_gh_unset(cmd: str) -> bool:
    """True when an earlier segment unsets/unexports GH_HOST/config before a merge.

    The merge child loses the exported var while the gate keeps the hook process
    env — fail closed rather than validating the wrong host/config.
    """
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    seen_unset = False
    for part in parts:
        if is_gh_pr_merge(part):
            if seen_unset:
                return True
            continue
        if _part_unsets_tracked_gh(part):
            seen_unset = True
    return False


def _part_loads_dynamic_builtin(part: str) -> bool:
    """True when ``enable -f`` loads ``gh`` or a shadowable prefix from a .so.

    ``enable -f /tmp/evil.so gh`` makes the next ``gh`` run the loaded builtin
    instead of the real binary the gate inspects. Dynamic name operands
    (``enable -f /tmp/evil.so \"$x\"``) fail closed the same way as ``hash -p``.
    """
    tokens = _shell_tokens(part)
    rest, _leading = _skip_leading_assignments(tokens)
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i < len(rest):
        nested = _nested_case_or_arm_body(rest, i)
        if nested is not None:
            return _part_loads_dynamic_builtin(nested)
    if i >= len(rest) or rest[i] != "enable":
        return False
    j = i + 1
    saw_f = False
    names: list[str] = []
    while j < len(rest):
        tok = rest[j]
        if tok == "--":
            names.extend(rest[j + 1 :])
            break
        if tok == "-f":
            saw_f = True
            j += 2
            continue
        if tok.startswith("-f") and not tok.startswith("--"):
            # sticky ``-f/tmp/evil.so``
            saw_f = True
            j += 1
            continue
        if tok.startswith("-") and not tok.startswith("--"):
            if "f" in tok[1:]:
                saw_f = True
                j += 2
                continue
            j += 1
            continue
        if tok.startswith("--"):
            j += 1
            continue
        names.append(tok)
        j += 1
    if not saw_f:
        return False
    targets = frozenset({"gh"}) | SHADOWABLE_PREFIXES
    if not names:
        # ``enable -f file`` with no name is opaque — fail closed.
        return True
    return any(
        n in targets
        or _dequote_shell_text(n) in targets
        or _var_target_dynamic(n)
        for n in names
    )


def _part_has_shell_mutation(part: str) -> bool:
    """True when the segment can install hidden merge side effects.

    Covers ``eval`` / ``source`` / ``.`` (redefine ``gh``), ``trap`` (EXIT
    handlers can run an unchecked merge after the inspected command), and
    ``enable -f`` (load a dynamic ``gh`` / prefix builtin).
    """
    tokens = _shell_tokens(part)
    rest, _leading = _skip_leading_assignments(tokens)
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i < len(rest) and rest[i] in ("eval", "source", ".", "trap"):
        return True
    if _part_loads_dynamic_builtin(part):
        return True
    dequoted = _dequote_shell_text(part)
    return dequoted != part and _part_loads_dynamic_builtin(dequoted)


def shell_mutation_before_merge(cmd: str) -> bool:
    """True when ``eval``/``source``/``.``/``trap``/``enable -f`` shares a merge.

    Order does not matter: a ``trap … EXIT`` *after* a validated merge still runs
    on shell exit and can perform an unchecked second merge.
    """
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    has_merge = False
    has_mutation = False
    for part in parts:
        if is_gh_pr_merge(part):
            has_merge = True
        elif _part_has_shell_mutation(part):
            has_mutation = True
        if has_merge and has_mutation:
            return True
    return False


def eval_before_merge(cmd: str) -> bool:
    """Backward-compatible alias for ``shell_mutation_before_merge`` (eval case)."""
    return shell_mutation_before_merge(cmd)


def _part_hash_override_risk(part: str) -> bool:
    """True when ``hash -p`` targets ``gh`` or a dynamically expanded name.

    ``hash -p /tmp/fake \"$x\"`` with ``x=gh`` remembers an attacker path for
    ``gh`` while the literal token is only ``$x``.
    """
    tokens = _shell_tokens(part)
    rest, _leading = _skip_leading_assignments(tokens)
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i < len(rest):
        nested = _nested_case_or_arm_body(rest, i)
        if nested is not None:
            return _part_hash_override_risk(nested)
    if i >= len(rest) or rest[i] != "hash":
        return False
    j = i + 1
    saw_p = False
    names: list[str] = []
    while j < len(rest):
        tok = rest[j]
        if tok == "-p":
            saw_p = True
            j += 2
            continue
        if tok.startswith("-p") and not tok.startswith("--") and tok != "-p":
            saw_p = True
            j += 1
            continue
        if tok.startswith("-"):
            j += 1
            continue
        names.append(tok)
        j += 1
    if not saw_p:
        return False
    if not names:
        # ``hash -p file`` with no name is opaque — fail closed.
        return True
    for n in names:
        if n == "gh" or _dequote_shell_text(n) == "gh" or _var_target_dynamic(n):
            return True
    return False


def _is_bash_cmds_override_target(name: str) -> bool:
    """True when ``name`` assigns ``BASH_CMDS[gh]`` (or a dynamic/opaque key).

    Bash inserts ``BASH_CMDS`` elements into the command hash table, so
    ``BASH_CMDS[gh]=/tmp/fake`` is equivalent to ``hash -p /tmp/fake gh``.
    """
    base = _env_key_base(name)
    if base != "BASH_CMDS":
        return False
    if "[" not in name:
        # Whole-array / scalar write is opaque — fail closed.
        return True
    idx = name.split("[", 1)[1]
    if idx.endswith("]"):
        idx = idx[:-1]
    idx_plain = _dequote_shell_text(idx.strip("'\""))
    if idx_plain == "gh" or idx_plain in SHADOWABLE_PREFIXES:
        return True
    if _var_target_dynamic(idx) or _var_target_dynamic(name):
        return True
    return False


def _part_bash_cmds_override(part: str) -> bool:
    """True when the segment writes ``BASH_CMDS[gh]`` / dynamic keys into the hash."""
    tokens = _shell_tokens(part)
    rest, leading = _skip_leading_assignments(tokens)
    if any(_is_bash_cmds_override_target(k) for k in leading):
        return True
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(rest):
        return False
    head = rest[i]
    nested = _nested_case_or_arm_body(rest, i)
    if nested is not None:
        return _part_bash_cmds_override(nested)
    m_head = ASSIGNMENT_RE.match(head)
    if m_head and _is_bash_cmds_override_target(m_head.group(1)):
        return True
    if head in ("export", "declare", "typeset", "local", "readonly"):
        for tok in rest[i + 1 :]:
            if tok.startswith("-") or tok.startswith("+"):
                continue
            key, _, _val = tok.partition("=")
            if _is_bash_cmds_override_target(key):
                return True
        return False
    if head == "printf":
        j = i + 1
        while j < len(rest):
            tok = rest[j]
            if tok in ("-v",):
                if j + 1 < len(rest) and (
                    _is_bash_cmds_override_target(rest[j + 1])
                    or _var_target_dynamic(rest[j + 1])
                ):
                    return True
                j += 2
                continue
            if tok.startswith("-") and tok != "-" and "=" not in tok:
                if "v" in tok[1:]:
                    sticky = tok.lstrip("-").lstrip("v")
                    if sticky and _is_bash_cmds_override_target(sticky):
                        return True
                j += 1
                continue
            break
        return False
    if head in ("read", "mapfile", "readarray"):
        for tok in rest[i + 1 :]:
            if tok.startswith("-"):
                continue
            if _is_bash_cmds_override_target(tok) or _var_target_dynamic(tok):
                return True
        return False
    return False


def redefines_gh(cmd: str) -> bool:
    """True when the command defines a ``gh`` function/alias/hash override.

    Also inspects a quote-stripped form so ``alias g'h'=…`` / ``g''h(){…}`` match
    after Bash quote-removal turns the name into ``gh``, and ``hash -p`` /
    ``BASH_CMDS[gh]=…`` with a dynamic name (``\"$x\"``) that may expand to ``gh``.
    """
    if not MERGE_RE.search(cmd):
        return False
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    if any(_part_hash_override_risk(p) for p in parts):
        return True
    if any(_part_bash_cmds_override(p) for p in parts):
        return True
    for candidate in (cmd, _dequote_shell_text(cmd)):
        if (
            GH_FUNC_RE.search(candidate)
            or GH_ALIAS_RE.search(candidate)
            or GH_HASH_RE.search(candidate)
        ):
            return True
    return False


def redefines_prefix_builtin(cmd: str) -> bool:
    """True when a stripped wrapper (``command``/``env``/…) is redefined before a merge."""
    if not MERGE_RE.search(cmd):
        return False
    for candidate in (cmd, _dequote_shell_text(cmd)):
        if PREFIX_FUNC_RE.search(candidate) or PREFIX_ALIAS_RE.search(candidate):
            return True
    return False


def _part_declares_nameref(part: str) -> bool:
    """True when the segment runs ``declare -n`` / ``typeset -n`` / ``local -n``."""
    tokens = _shell_tokens(part)
    rest, _leading = _skip_leading_assignments(tokens)
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(rest) or rest[i] not in ("declare", "typeset", "local"):
        return False
    for tok in rest[i + 1 :]:
        if tok.startswith("-") and "=" not in tok:
            if "n" in tok[1:]:
                return True
            continue
        if tok.startswith("+") and "=" not in tok:
            if "n" in tok[1:]:
                return True
            continue
        break
    return False


def nameref_with_merge(cmd: str) -> bool:
    """True when a nameref appears in a compound command that also merges.

    ``declare -n host=GH_HOST; host=ghe.example; gh … pr merge`` mutates the
    tracked export without naming ``GH_HOST`` in a literal assignment.
    """
    if not MERGE_RE.search(cmd):
        return False
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    return any(_part_declares_nameref(p) for p in parts)


def defines_command_not_found_handle(cmd: str) -> bool:
    """True when the command locally defines ``command_not_found_handle``.

    ``command_not_found_handle(){ /tmp/evil; }; gx … pr merge`` never matches
    ``is_gh_pr_merge`` / ``MERGE_RE``, but Bash still runs the handler for the
    unresolved ``gx``. Fail closed whenever that definition shares a loose
    ``pr merge`` shape (same trigger as inherited CNF).
    """
    if not (
        MERGE_RE.search(cmd)
        or _PR_MERGE_LOOSE_RE.search(cmd)
        or _PR_MERGE_LOOSE_RE.search(_dequote_shell_text(cmd))
    ):
        return False
    for candidate in (cmd, _dequote_shell_text(cmd)):
        if CNF_FUNC_RE.search(candidate):
            return True
    return False


def inherited_shadowing_function(
    cmd: str, env: dict[str, str] | None = None
) -> bool:
    """True when the process inherits an exported Bash function that shadows merges.

    Bash stores ``export -f gh`` as ``BASH_FUNC_gh%%`` in the environment; a plain
    ``gh -R safe pr merge`` then runs that function while the gate only sees the
    apparent safe argv. Same for shadowable wrappers (``command``/``env``/…).

    Also covers ``command_not_found_handle``: an unresolved name like ``gx … pr
    merge`` invokes that handler with the apparent argv, which can run a real
    merge without a literal ``gh`` token (so ``MERGE_RE`` alone is insufficient).
    """
    e = os.environ if env is None else env
    has_cnf = "BASH_FUNC_command_not_found_handle%%" in e
    has_shadow = any(
        f"BASH_FUNC_{name}%%" in e for name in ("gh", *sorted(SHADOWABLE_PREFIXES))
    )
    if not has_cnf and not has_shadow:
        return False
    if has_shadow and MERGE_RE.search(cmd):
        return True
    if has_cnf and (
        MERGE_RE.search(cmd)
        or _PR_MERGE_LOOSE_RE.search(cmd)
        or _PR_MERGE_LOOSE_RE.search(_dequote_shell_text(cmd))
    ):
        return True
    return False


def _part_sets_bash_env(part: str) -> bool:
    """True when the segment assigns ``BASH_ENV`` (sourced by non-interactive Bash)."""
    tokens = _shell_tokens(part)
    rest, leading = _skip_leading_assignments(tokens)
    if any(_env_key_base(k) == "BASH_ENV" for k in leading):
        return True
    env_assigns, _cleared = _env_wrapper_state(rest)
    if any(_env_key_base(k) == "BASH_ENV" for k in env_assigns):
        return True
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(rest):
        return False
    head = rest[i]
    if head in ("export", "declare", "typeset", "local", "readonly"):
        for tok in rest[i + 1 :]:
            if tok.startswith("-") or tok.startswith("+"):
                continue
            key = tok.split("=", 1)[0]
            if _env_key_base(key) == "BASH_ENV":
                return True
        return False
    if head == "printf":
        j = i + 1
        while j < len(rest):
            tok = rest[j]
            if tok in ("-v",):
                if j + 1 < len(rest) and _env_key_base(rest[j + 1]) == "BASH_ENV":
                    return True
                j += 2
                continue
            if tok.startswith("-") and tok != "-" and "=" not in tok:
                if "v" in tok[1:]:
                    sticky = tok.lstrip("-").lstrip("v")
                    if sticky and _env_key_base(sticky) == "BASH_ENV":
                        return True
                j += 1
                continue
            break
        return False
    if head in ("read", "mapfile", "readarray"):
        for tok in rest[i + 1 :]:
            if tok.startswith("-"):
                continue
            if _env_key_base(tok) == "BASH_ENV":
                return True
        return False
    return False


def inherited_bash_env(cmd: str, env: dict[str, str] | None = None) -> bool:
    """True when nonempty ``BASH_ENV`` may source unchecked defs around a merge.

    Non-interactive Bash sources ``BASH_ENV``; a non-exported ``gh()`` defined
    there never appears as ``BASH_FUNC_gh%%`` in the gate process environment, so
    ``inherited_shadowing_function`` misses it. Fail closed on inherited or
    command-scoped ``BASH_ENV``.
    """
    if not MERGE_RE.search(cmd):
        return False
    e = os.environ if env is None else env
    if (e.get("BASH_ENV") or "").strip():
        return True
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    return any(_part_sets_bash_env(p) for p in parts)


def _part_enables_set_option(part: str, letter: str, option: str) -> bool:
    """True when the segment turns on ``set -<letter>`` / ``set -o <option>``."""
    tokens = _shell_tokens(part)
    rest, _leading = _skip_leading_assignments(tokens)
    i = 0
    while i < len(rest) and rest[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(rest) or rest[i] != "set":
        return False
    j = i + 1
    while j < len(rest):
        tok = rest[j]
        if tok in ("-o",):
            if j + 1 < len(rest) and rest[j + 1] == option:
                return True
            j += 2
            continue
        if tok.startswith("--"):
            j += 1
            continue
        if tok.startswith("+"):
            # ``set +a`` / ``set +k`` disables; ignore for enable detection.
            j += 1
            continue
        if tok.startswith("-") and letter in tok[1:]:
            return True
        j += 1
    return False


def _part_enables_allexport(part: str) -> bool:
    """True when the segment turns on ``set -a`` / ``set -o allexport``."""
    return _part_enables_set_option(part, "a", "allexport")


def _part_enables_keyword(part: str) -> bool:
    """True when the segment turns on ``set -k`` / ``set -o keyword``."""
    return _part_enables_set_option(part, "k", "keyword")


def _set_option_before_merge(
    cmd: str, enable_fn
) -> bool:
    """True when ``enable_fn(part)`` fires in an earlier segment before a merge."""
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    seen = False
    for part in parts:
        if is_gh_pr_merge(part):
            if seen:
                return True
            continue
        if enable_fn(part):
            seen = True
    return False


def allexport_before_merge(cmd: str) -> bool:
    """True when ``set -a``/allexport precedes a merge (assignments become exports).

    Modeling ``set +a`` toggles is brittle; once allexport was enabled in an
    earlier segment, fail closed for any later merge in the compound command.
    """
    return _set_option_before_merge(cmd, _part_enables_allexport)


def keyword_before_merge(cmd: str) -> bool:
    """True when ``set -k``/keyword precedes a merge (trailing assigns become env).

    Under keyword mode, ``gh … pr merge 42 GH_HOST=…`` exports the trailing
    assignment to the real child while the gate never sees it — fail closed.
    """
    return _set_option_before_merge(cmd, _part_enables_keyword)


def _repo_operand_unresolvable(repo: str | None) -> bool:
    """True when -R/--repo/GH_REPO still contains shell expansion."""
    if not repo:
        return False
    return "$" in repo or "`" in repo


def _env_overlay_unresolvable(val: str | None) -> bool:
    """True when a command-scoped env overlay still needs shell expansion.

    Covers ``$`` / backticks and leading ``~`` (Bash tilde-expands unquoted
    ``~/…`` / ``~user/…``; after ``shlex`` we cannot tell quoting, so fail closed).
    """
    if not val:
        return False
    if _repo_operand_unresolvable(val):
        return True
    return val.startswith("~")


def _normalize_repo_operand(val: str) -> str:
    return "$UNRESOLVED" if _repo_operand_unresolvable(val) else val


def repo_from_pull_url_match(m: re.Match[str]) -> str:
    """Build `HOST/OWNER/REPO` from a PULL_URL match (dotcom kept explicit)."""
    host, owner, name = m.group(1), m.group(2), m.group(3)
    if host.lower() in DOTCOM_PULL_HOSTS:
        return f"github.com/{owner}/{name}"
    return f"{host}/{owner}/{name}"


def _apply_gh_host(repo: str | None, assignments: dict[str, str]) -> str | None:
    """Prefix a hostless OWNER/REPO with a GH_HOST assignment.

    Matches ``gh help environment``: GH_HOST (leading or via ``env``) selects
    the API host when the repository slug does not already embed one. Dotcom is
    kept as an explicit ``github.com/…`` slug so API calls can pass
    ``--hostname`` and override a process-level Enterprise GH_HOST. Dynamic
    hosts fail closed.
    """
    if not repo or repo == "$UNRESOLVED":
        return repo
    parts = [p for p in repo.strip().strip("/").split("/") if p]
    if len(parts) >= 3:
        return repo
    if "GH_HOST" not in assignments:
        return repo
    gh_host = assignments.get("GH_HOST")
    # Empty ``GH_HOST=`` clears the host → gh defaults to github.com.
    if gh_host is None or gh_host == "":
        return f"github.com/{repo}"
    if _repo_operand_unresolvable(gh_host):
        return "$UNRESOLVED"
    if gh_host.lower() in DOTCOM_PULL_HOSTS:
        return f"github.com/{repo}"
    return f"{gh_host}/{repo}"


def extract_repo_resolution(cmd: str) -> tuple[str | None, bool]:
    """Return ``(repo_slug|None|$UNRESOLVED, scrub_process_gh_repo)``.

    ``scrub_process_gh_repo`` is True when the command clears GH_REPO for the
    child (empty ``GH_REPO=``, ``env -u GH_REPO``, ``env -i``) so gate ``gh``
    calls must drop the hook process GH_REPO and resolve the tool cwd instead.
    """
    tokens = _shell_tokens(cmd)
    rest, assignments = _skip_leading_assignments(tokens)
    # ``env NAME=VALUE … gh`` overlays leading assignments (matches the child env).
    env_assigns, cleared = _env_wrapper_state(rest)
    assignments = {**assignments, **env_assigns}
    if "GH_HOST" in cleared and "GH_HOST" not in env_assigns:
        # Child has no GH_HOST → gh defaults to github.com; say so explicitly.
        assignments["GH_HOST"] = "github.com"
    # Empty ``GH_REPO=`` or ``-u GH_REPO`` clears the selector for the child.
    cleared_gh_repo = "GH_REPO" in cleared
    if "GH_REPO" in assignments and assignments.get("GH_REPO") == "":
        cleared_gh_repo = True
    elif cleared_gh_repo and "GH_REPO" not in env_assigns:
        assignments.pop("GH_REPO", None)
    found: str | None = None
    # Only scan gh argv (not `env -uGH_REPO` / similar wrappers — those contain
    # the letter R and must not be parsed as bundled merge short flags).
    try:
        i = rest.index("gh")
    except ValueError:
        i = 0
    while i < len(rest):
        tok = rest[i]
        if tok == "--":
            # Option terminator — later tokens are positionals (e.g. branch
            # ``-Rowner/branch``), not repository flags.
            break
        if tok.startswith("-"):
            next_i, repo_val, missing = _consume_merge_argv_flag(rest, i)
            if missing and repo_val is None and tok in ("-R", "--repo"):
                return None, cleared_gh_repo
            if repo_val is not None:
                found = _normalize_repo_operand(repo_val)
            i = next_i
            continue
        i += 1
    if found is not None:
        # Explicit -R wins; process GH_REPO is irrelevant for repo identity.
        return _apply_gh_host(found, assignments), False
    if "GH_REPO" in assignments:
        gh_repo = assignments.get("GH_REPO")
        if gh_repo == "":
            return None, True
        return _apply_gh_host(_normalize_repo_operand(gh_repo), assignments), False
    if cleared_gh_repo:
        return None, True
    return None, False


def extract_repo(cmd: str) -> str | None:
    """Return the last -R/--repo from argv, or a leading/env GH_REPO= assignment."""
    repo, _scrub = extract_repo_resolution(cmd)
    return repo


def extract_merge_selector(cmd: str) -> str | None:
    """Positional selector after `merge`, or None when merging the current branch."""
    tokens, _ = _skip_leading_assignments(_shell_tokens(cmd))
    try:
        gh_i = tokens.index("gh")
        pr_i = next(i for i in range(gh_i + 1, len(tokens)) if tokens[i] == "pr")
        merge_i = next(i for i in range(pr_i + 1, len(tokens)) if tokens[i] == "merge")
    except (ValueError, StopIteration):
        return None
    i = merge_i + 1
    while i < len(tokens):
        tok = tokens[i]
        if tok == "--":
            # Option terminator — next token is the selector even if it starts with -.
            if i + 1 >= len(tokens):
                return None
            nxt = tokens[i + 1]
            if nxt in {")", "fi", "done", "esac"}:
                return None
            return nxt
        if tok.startswith("-"):
            next_i, _repo_val, _missing = _consume_merge_argv_flag(tokens, i)
            i = next_i
            continue
        # Trailing subshell closer etc.
        if tok in {")", "fi", "done", "esac"}:
            i += 1
            continue
        return tok
    return None


def is_pull_url_selector(selector: str) -> re.Match[str] | None:
    """Match only when the *entire* merge selector is a pull URL (not a substring)."""
    return PULL_URL.fullmatch(selector.strip())


def has_literal_repo(part: str) -> bool:
    """True when the merge names a concrete owner/repo (-R, GH_REPO=, or pull URL)."""
    repo = extract_repo(part)
    if repo and repo != "$UNRESOLVED" and "/" in repo:
        return True
    selector = extract_merge_selector(part)
    if selector and is_pull_url_selector(selector):
        return True
    return False


COMPOUND_MERGE_MSG = (
    "review-gate: compound shell command with `gh pr merge`; "
    "pass literal `-R owner/repo` on each merge "
    "(cd/export/subshell/cwd chains are not modeled)"
)


def extract_pr_and_repo(cmd: str) -> tuple[int | None, str | None]:
    """Legacy helper: numeric selector only. Prefer resolve_pr_number for merges."""
    repo = extract_repo(cmd)
    selector = extract_merge_selector(cmd)
    if selector and selector.isdigit():
        return int(selector), repo
    return None, repo


def _apply_overlay_env_var(
    env: dict[str, str], overlays: dict[str, str], key: str
) -> None:
    """Set or clear ``key`` on ``env`` from a command-scoped overlay.

    Callers must reject unresolvable values via ``gh_config_overlay_unresolved``
    before relying on the resulting env (we never silently keep the hook value).
    """
    if key not in overlays:
        return
    val = overlays[key]
    if val == "":
        env.pop(key, None)
    elif not _env_overlay_unresolvable(val):
        env[key] = val


def gh_config_overlay_unresolved(cmd: str) -> bool:
    """True when a command-scoped gh config/host path still needs shell expansion.

    Bash expands ``GH_CONFIG_DIR="$HOME/enterprise"`` and unquoted
    ``GH_CONFIG_DIR=~/enterprise`` for the merge child, but our parser only
    sees the raw ``$HOME/…`` / ``~/…`` — fail closed rather than checking
    against the hook's inherited config dir/host.
    """
    tokens = _shell_tokens(cmd)
    rest, leading = _skip_leading_assignments(tokens)
    env_assigns, _cleared = _env_wrapper_state(rest)
    overlays = {**leading, **env_assigns}
    for key in GH_TRACKED_ENV_VARS:
        if key not in overlays:
            continue
        val = overlays[key]
        if val and _env_overlay_unresolvable(val):
            return True
    return False


def _env_has_chdir(part: str) -> bool:
    """True when ``env -C`` / ``--chdir`` appears before ``gh``."""
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    try:
        env_i = next(i for i, t in enumerate(tokens) if t == "env")
        gh_i = next(i for i, t in enumerate(tokens) if t == "gh")
    except StopIteration:
        return False
    if env_i >= gh_i:
        return False
    i = env_i + 1
    while i < gh_i:
        tok = tokens[i]
        if tok in ("-C", "--chdir") or tok.startswith("--chdir="):
            return True
        if tok.startswith("-C") and tok != "-C":
            return True
        if ASSIGNMENT_RE.match(tok):
            i += 1
            continue
        if tok.startswith("-"):
            base = tok.split("=", 1)[0]
            if base in ENV_VALUE_FLAGS:
                i += 2
                continue
            i += 1
            continue
        break
    return False


def _part_has_relative_gh_config(part: str) -> bool:
    """True when the segment sets a relative GH_CONFIG_DIR/XDG/HOME overlay."""
    tokens = _shell_tokens(part)
    rest, leading = _skip_leading_assignments(tokens)
    env_assigns, _cleared = _env_wrapper_state(rest)
    overlays = {**leading, **env_assigns}
    for key in GH_CONFIG_LOCATION_VARS:
        if key not in overlays:
            continue
        val = overlays[key]
        if not val or _env_overlay_unresolvable(val):
            continue
        if not os.path.isabs(val):
            return True
    return False


def _part_may_chdir(part: str) -> bool:
    """True when the segment can change cwd (cd/pushd/popd/env -C/subshell)."""
    if _env_has_chdir(part) or bool(SUBSHELL_CD_RE.search(part)):
        return True
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    i = _index_after_env_wrapper(tokens)
    while i < len(tokens) and tokens[i] in SHELL_PREFIX_KEYWORDS:
        i += 1
    if i >= len(tokens):
        return False
    head = tokens[i].lstrip("(")
    return head in DIR_BUILTINS or head == "popd"


def _inherited_relative_gh_config() -> bool:
    """True when the process env already has a relative GH config location."""
    for key in GH_CONFIG_LOCATION_VARS:
        val = os.environ.get(key)
        if not val or _env_overlay_unresolvable(val):
            continue
        if not os.path.isabs(val):
            return True
    return False


def gh_config_relative_after_chdir(cmd: str) -> bool:
    """True when a relative gh config path may resolve against a different cwd.

    Covers command-scoped overlays, **inherited** ``GH_CONFIG_DIR``/XDG/HOME,
    ``env -C``, subshell ``(cd|pushd|…)``, and earlier compound ``cd``/``pushd``
    segments (chain splitting drops those from the merge argv, but the child
    still inherits their cwd).
    """
    chains = split_shell_chains(cmd)
    parts = [p for p, _ in chains] if chains else [cmd]
    has_relative = any(_part_has_relative_gh_config(p) for p in parts) or (
        _inherited_relative_gh_config()
    )
    if not has_relative:
        return False
    if any(_part_may_chdir(p) for p in parts):
        return True
    # Full-string subshell / env -C even when not split into its own part.
    return bool(SUBSHELL_CD_RE.search(cmd)) or _env_has_chdir(cmd)


def _path_has_relative_component(path: str) -> bool:
    """True when ``PATH`` contains ``.`` / empty / other non-absolute entries."""
    for entry in path.split(os.pathsep):
        # Empty component means cwd (relative), same as ``.``.
        if entry == "" or entry in (".", "..") or not os.path.isabs(entry):
            return True
    return False


def _inherited_relative_path(env: dict[str, str] | None = None) -> bool:
    """True when the process ``PATH`` includes a relative lookup component."""
    e = os.environ if env is None else env
    path = e.get("PATH")
    if path is None:
        return False
    return _path_has_relative_component(path)


def relative_path_after_chdir(
    cmd: str, env: dict[str, str] | None = None
) -> bool:
    """True when a relative inherited PATH may resolve ``gh`` after a chdir.

    ``cd /tmp/fake; gh -R owner/safe pr merge 1`` with inherited ``PATH``
    containing ``.`` runs ``/tmp/fake/gh`` while the gate still uses start_cwd.
    """
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    if not any(is_gh_pr_merge(p) for p in parts):
        return False
    if not _inherited_relative_path(env):
        return False
    if any(_part_may_chdir(p) for p in parts):
        return True
    return bool(SUBSHELL_CD_RE.search(cmd)) or _env_has_chdir(cmd)


def _tokens_have_pr_merge(tokens: list[str]) -> bool:
    try:
        pr_i = next(i for i, t in enumerate(tokens) if t == "pr")
        next(i for i in range(pr_i + 1, len(tokens)) if tokens[i] == "merge")
        return True
    except StopIteration:
        return False


def env_split_string_merge_risk(part: str) -> bool:
    """True when ``env -S``/``--split-string`` can construct a ``gh pr merge``.

    GNU env splits the ``-S`` operand into argv, so ``env -S 'g''h -R …' pr merge``
    runs a real merge while literal ``gh`` never appears as its own token.
    """
    tokens, _ = _skip_leading_assignments(_shell_tokens(part))
    try:
        env_i = next(i for i, t in enumerate(tokens) if t == "env")
    except StopIteration:
        return False
    operands: list[str] = []
    i = env_i + 1
    while i < len(tokens):
        tok = tokens[i]
        if ASSIGNMENT_RE.match(tok):
            i += 1
            continue
        if tok in ("-S", "--split-string"):
            if i + 1 < len(tokens):
                operands.append(tokens[i + 1])
            i += 2
            continue
        if tok.startswith("--split-string="):
            operands.append(tok.split("=", 1)[1])
            i += 1
            continue
        if tok.startswith("-"):
            if tok in ("-", "-i", "--ignore-environment"):
                i += 1
                continue
            if tok.startswith("--") and "=" in tok:
                i += 1
                continue
            base = tok.split("=", 1)[0]
            if base in ENV_VALUE_FLAGS:
                i += 2
                continue
            i += 1
            continue
        break
    if not operands:
        return False
    if _tokens_have_pr_merge(tokens):
        return True
    for op in operands:
        if MERGE_RE.search(op) or _tokens_have_pr_merge(_shell_tokens(op)):
            return True
    return False


def _absolutize_config_path(val: str, cwd: str | None) -> str:
    """Resolve a relative gh config path against the tool/merge cwd."""
    if not val or os.path.isabs(val) or _env_overlay_unresolvable(val):
        return val
    base = cwd if cwd is not None else os.getcwd()
    return os.path.normpath(os.path.join(base, val))


def _child_gh_env(
    cmd: str, scrub_gh_repo: bool, cwd: str | None = None
) -> dict[str, str] | None:
    """Build a subprocess env mirroring command-scoped gh config for gate ``gh``.

    Propagates ``GH_HOST`` / ``GH_REPO`` / ``GH_CONFIG_DIR`` / ``XDG_CONFIG_HOME`` /
    ``HOME`` so host selection and config dirs match the merge child. Relative
    config paths are resolved against ``cwd`` (the tool working directory) so the
    gate sees the same directory Bash would for the merge child.
    """
    tokens = _shell_tokens(cmd)
    rest, leading = _skip_leading_assignments(tokens)
    env_assigns, cleared = _env_wrapper_state(rest)
    overlays = {**leading, **env_assigns}
    touches = (
        "GH_HOST" in overlays
        or "GH_REPO" in overlays
        or any(k in overlays for k in GH_CONFIG_LOCATION_VARS)
        or bool(cleared & GH_TRACKED_ENV_VARS)
        or scrub_gh_repo
    )
    if not touches:
        return None
    env = os.environ.copy()
    if "GH_HOST" in cleared and "GH_HOST" not in env_assigns:
        env.pop("GH_HOST", None)
    elif "GH_HOST" in overlays:
        _apply_overlay_env_var(env, overlays, "GH_HOST")
    if (
        scrub_gh_repo
        or ("GH_REPO" in cleared and "GH_REPO" not in env_assigns)
        or overlays.get("GH_REPO") == ""
    ):
        env.pop("GH_REPO", None)
    elif "GH_REPO" in overlays and overlays["GH_REPO"]:
        val = overlays["GH_REPO"]
        if not _repo_operand_unresolvable(val):
            env["GH_REPO"] = val
    for key in GH_CONFIG_LOCATION_VARS:
        if key in cleared and key not in env_assigns:
            env.pop(key, None)
        else:
            _apply_overlay_env_var(env, overlays, key)
            if key in env and env[key]:
                env[key] = _absolutize_config_path(env[key], cwd)
    return env


def resolve_pr_number(
    cmd: str, cwd: str | None = None
) -> tuple[int | None, str | None, str | None, bool]:
    """Resolve gh pr merge selector → (number, repo, error, scrub_gh_repo).

    Supports number, pull URL (including owner/repo from the URL), branch name,
    and omitted selector (current branch) via `gh pr view`.
    """
    repo, scrub_gh_repo = extract_repo_resolution(cmd)
    if repo == "$UNRESOLVED":
        return None, None, (
            "review-gate: dynamic `-R`/`--repo`/GH_REPO operand (e.g. \"$VAR\"); "
            "pass a literal `owner/repo`"
        ), False
    if gh_config_overlay_unresolved(cmd):
        return None, None, (
            "review-gate: dynamic GH_CONFIG_DIR/XDG_CONFIG_HOME/HOME/GH_HOST "
            "(e.g. \"$HOME/…\" or \"~/…\"); pass a literal path or unset the var"
        ), scrub_gh_repo
    if gh_config_relative_after_chdir(cmd):
        return None, None, (
            "review-gate: relative GH_CONFIG_DIR/XDG_CONFIG_HOME/HOME under "
            "env -C/--chdir (or subshell cd); pass an absolute config path"
        ), scrub_gh_repo
    selector = extract_merge_selector(cmd)
    if selector and selector.isdigit():
        return int(selector), repo, None, scrub_gh_repo
    if selector:
        m_url = is_pull_url_selector(selector)
        if m_url:
            # gh resolves the repository from the URL selector even when -R
            # disagrees (e.g. `gh pr merge https://…/target/pull/7 -R owner/safe`).
            url_repo = repo_from_pull_url_match(m_url)
            return int(m_url.group(4)), url_repo, None, False
    child_env = _child_gh_env(cmd, scrub_gh_repo, cwd=cwd)
    # ``gh pr view [<number>|<url>|<branch>] [flags]`` — selector follows ``view``.
    args = ["gh", "pr", "view"]
    if selector:
        # Branches that start with `-` need `--` (same as `gh pr merge -- -release`).
        if selector.startswith("-"):
            args.extend(["--", selector])
        else:
            args.append(selector)
    args.extend(["--json", "number,url"])
    if repo:
        args.extend(["-R", repo])
    try:
        proc = subprocess.run(
            args,
            capture_output=True,
            text=True,
            cwd=cwd or None,
            env=child_env,
            timeout=20,
        )
    except (OSError, subprocess.SubprocessError) as e:
        return None, repo, f"review-gate: could not resolve PR via gh: {e}", scrub_gh_repo
    if proc.returncode != 0 or not proc.stdout.strip():
        detail = (proc.stderr or proc.stdout or "gh pr view failed").strip()
        return (
            None,
            repo,
            f"review-gate: could not resolve PR from merge selector: {detail}",
            scrub_gh_repo,
        )
    try:
        data = json.loads(proc.stdout)
        number = int(data["number"])
    except (ValueError, KeyError, TypeError, json.JSONDecodeError) as e:
        return (
            None,
            repo,
            f"review-gate: could not parse gh pr view output: {e}",
            scrub_gh_repo,
        )
    if not repo:
        m_url = PULL_URL.search(data.get("url") or "")
        if m_url:
            repo = repo_from_pull_url_match(m_url)
    return number, repo, None, scrub_gh_repo


def payload_cwd(payload: dict, inp: dict) -> str:
    """AEC puts cwd at the top level; some harnesses nest it under tool_input."""
    for candidate in (
        payload.get("cwd"),
        payload.get("working_directory"),
        inp.get("working_directory"),
        inp.get("cwd"),
    ):
        if candidate:
            return str(candidate)
    return os.getcwd()


def _cd_target_unresolvable(target: str | None) -> bool:
    """True when the guard cannot know the post-cd directory statically."""
    if not target or target == "-":
        return True
    if "$" in target or "`" in target:
        return True
    return False


DIR_BUILTINS = frozenset({"cd", "pushd"})
# Sourced scripts run in the current shell and may change cwd.
SOURCE_BUILTINS = frozenset({"source", "."})
# Control-flow prefixes where a later `cd` is a real builtin (`if cd …`).
SHELL_KEYWORDS = frozenset(
    {
        "if",
        "then",
        "else",
        "elif",
        "while",
        "until",
        "for",
        "do",
        "case",
        "select",
        "time",
        "!",
    }
)


def parse_dir_builtin(part: str, builtin: str) -> str | None:
    """Return the directory operand of cd/pushd, skipping -L/-P/-- options.

    None means bare builtin, `cd -`, or no directory token (treat as unresolvable).
    """
    try:
        tokens = shlex.split(part, posix=True)
    except ValueError:
        tokens = part.split()
    if not tokens:
        return None
    head = tokens[0].lstrip("(")
    if head != builtin:
        return None
    i = 1
    while i < len(tokens):
        tok = tokens[i]
        if tok == "--":
            i += 1
            break
        if tok.startswith("-") and tok != "-":
            i += 1
            continue
        break
    if i >= len(tokens):
        return None
    return tokens[i].rstrip(")").strip("'\"")


def _leading_dir_builtin(tokens: list[str]) -> str | None:
    """Return cd/pushd/popd if it is the first actionable token (incl. `(cd`)."""
    if not tokens:
        return None
    head = tokens[0].lstrip("(")
    if head in DIR_BUILTINS or head == "popd":
        return head
    return None


def iter_merge_segments(
    cmd: str, start_cwd: str
) -> tuple[list[tuple[str, str]], str | None]:
    """Return ((segment, cwd)…, error).

    Quote-aware split on `&&`, `||`, `|`, `;`, `&`, and newlines.

    Policy (fail closed): any *compound* command (more than one shell segment)
    requires a literal `-R`/`--repo`/GH_REPO=/pull-URL on each merge. We do not
    model cd/export/subshell/cwd interactions across segments — that rat-hole
    kept producing review findings. Prefer `gh -R owner/repo pr merge <n>`.
    """
    chains = split_shell_chains(cmd)
    compound = len(chains) > 1
    out: list[tuple[str, str]] = []
    for part, _sep_after in chains:
        if not is_gh_pr_merge(part):
            continue
        toks = _shell_tokens(part)
        merge_verbs = sum(
            1
            for i, t in enumerate(toks)
            if t == "merge" and "pr" in toks[:i] and "gh" in toks[:i]
        )
        if merge_verbs > 1:
            return [], (
                "review-gate: multiple `gh pr merge` invocations in one shell "
                "segment; run them as separate commands"
            )
        if not gh_is_direct_command(part):
            return [], (
                "review-gate: `gh pr merge` must be the directly executed command "
                "(no ssh/xargs/docker/… wrappers); run `gh -R owner/repo pr merge <n>`"
            )
        if scoped_dir_requires_repo(part) and not has_literal_repo(part):
            return [], (
                "review-gate: command-scoped directory change detected "
                "(e.g. `env -C`/`--chdir` / subshell `cd`); pass `-R owner/repo` explicitly"
            )
        if sets_git_location(part) and not has_literal_repo(part):
            return [], (
                "review-gate: GIT_DIR/GIT_CONFIG_* without literal `-R owner/repo`; "
                "pass `-R` (git location/config env is not modeled)"
            )
        if compound and not has_literal_repo(part):
            return [], COMPOUND_MERGE_MSG
        # Always evaluate against the tool cwd; literal -R selects the repo.
        out.append((part, start_cwd))
    return out, None


def check_one(segment: str, cwd: str | None) -> str | None:
    number, repo, err, scrub_gh_repo = resolve_pr_number(segment, cwd=cwd)
    if err:
        return err
    if number is None:
        return "review-gate: could not parse PR number from `gh pr merge` command"
    child_env = _child_gh_env(segment, scrub_gh_repo, cwd=cwd)
    try:
        with gate.gh_subprocess_env(child_env):
            hostname, owner, name = gate.parse_repo_with_host(
                repo, cwd=cwd, env=child_env
            )
            pr = gate.pr_payload(owner, name, number, hostname=hostname)
            reasons = gate.evaluate(pr)
    except Exception as e:  # noqa: BLE001
        # Fail closed: infra / GraphQL errors must not silently allow merges.
        return f"review-gate: gate check failed: {e}"
    if reasons:
        return "review-gate blocked merge:\n" + "\n".join(f"- {r}" for r in reasons)
    return None


def check_command(cmd: str, cwd: str | None = None) -> str | None:
    # Inspect executable/expanding heredocs before stripping their bodies.
    if executable_heredoc_merge(cmd):
        return (
            "review-gate: heredoc body contains `gh pr merge` "
            "(executed by `bash <<` / expanded unquoted); run literal "
            "`gh -R owner/repo pr merge <n>` without embedding it in a heredoc"
        )
    cmd = strip_heredoc_bodies(cmd)
    parts = [p for p, _ in split_shell_chains(cmd)] or [cmd]
    # `a=(gh … pr merge); "${a[@]}"` — array-assembled merges bypass token checks.
    if array_assembled_merge(cmd) or any(array_assembled_merge(p) for p in parts):
        return (
            "review-gate: array-assembled `gh pr merge` "
            "(e.g. `a=(gh … pr merge); \"${a[@]}\"`); run literal "
            "`gh -R owner/repo pr merge <n>` without array argv"
        )
    # `set -- gh … pr; set -- "$@" merge; "$@"` — positional-parameter assembly.
    if positional_assembled_merge(cmd) or any(
        positional_assembled_merge(p) for p in parts
    ):
        return (
            "review-gate: positional-parameter-assembled `gh pr merge` "
            "(e.g. `set -- gh … pr; set -- \"$@\" merge; \"$@\"`); run literal "
            "`gh -R owner/repo pr merge <n>` without `$@`/`$*` argv"
        )
    # Quote-smashed `g''h` inside `bash -c` / eval — Bash concatenates to `gh`.
    if quote_smashed_merge(cmd) or any(quote_smashed_merge(p) for p in parts):
        return (
            "review-gate: quote-concatenated `gh` with `pr merge` "
            "(e.g. `bash -c 'g''h … pr merge'`); run literal "
            "`gh -R owner/repo pr merge <n>`"
        )
    # `bash -c 'x=g; x+=h; "$x" … pr merge'` — nested dynamic assembly.
    if opaque_shell_wrapper_pr_merge(cmd) or any(
        opaque_shell_wrapper_pr_merge(p) for p in parts
    ):
        return (
            "review-gate: shell-wrapped dynamic `pr merge` "
            "(e.g. `bash -c` / `eval` assembling `gh`); run literal "
            "`gh -R owner/repo pr merge <n>` directly"
        )
    # Every segment — including those after a literal `gh pr merge` — must not
    # hide a dynamically named merge (`$'\\x67\\x68'`, `./[g]h`, …).
    if any(dynamic_gh_pr_merge(p) for p in parts):
        return (
            "review-gate: dynamic `gh` executable name "
            "(e.g. $'\\x67\\x68' / $(…) / `…` / ./[g]h); "
            "run literal `gh -R owner/repo pr merge <n>`"
        )
    # `gh "$x" "$y"` / `gh pr "$y"` with x=pr y=merge — dynamic subcommands.
    if any(dynamic_gh_subcommand_merge(p) for p in parts):
        return (
            "review-gate: dynamic `gh` subcommand "
            "(e.g. `gh \"$x\" \"$y\"` / `gh pr \"$m\"`); "
            "run literal `gh -R owner/repo pr merge <n>`"
        )
    # `c=gh; p=pr; m=merge; "$c" "$p" "$m" …` — fully variable-assembled merge.
    if variable_assembled_merge(cmd) or any(
        variable_assembled_merge(p) for p in parts
    ):
        return (
            "review-gate: variable-assembled `gh pr merge` "
            "(e.g. `c=gh; p=pr; m=merge; \"$c\" \"$p\" \"$m\" …`); "
            "run literal `gh -R owner/repo pr merge <n>`"
        )
    # `gh pr merge 42 "$(printf -- -Rowner/target)"` — dynamic argv may become -R.
    if any(dynamic_merge_argv(p) for p in parts):
        return (
            "review-gate: dynamic argv after `gh pr merge` "
            "(e.g. `\"$(printf -- -Rowner/repo)\"`); pass literal flags and selectors"
        )
    # `env -S` can assemble `gh` inside the split-string operand.
    if any(env_split_string_merge_risk(p) for p in parts):
        return (
            "review-gate: `env -S`/`--split-string` with `pr merge` "
            "(can construct `gh` argv); run literal `gh -R owner/repo pr merge <n>`"
        )
    # Relative config after cd/pushd in an earlier segment (full command).
    if gh_config_relative_after_chdir(cmd):
        return (
            "review-gate: relative GH_CONFIG_DIR/XDG_CONFIG_HOME/HOME under "
            "cd/pushd/env -C (cwd differs from the gate); pass an absolute path"
        )
    # Inherited PATH with `.` / relative entries + cd can swap which `gh` runs.
    if relative_path_after_chdir(cmd):
        return (
            "review-gate: relative inherited PATH under cd/pushd/env -C "
            "(cwd changes which `gh` is found); use an absolute-only PATH or "
            "run `gh -R owner/repo pr merge <n>` without changing directories"
        )
    # PATH=… / env -u PATH can replace the ``gh`` binary the shell runs.
    if path_override_for_merge(cmd):
        return (
            "review-gate: command-scoped PATH override with `gh pr merge` "
            "(can swap the `gh` binary); unset PATH for the merge command"
        )
    # Prior `export`/`declare -x` of GH_HOST=… is invisible to the merge-segment env.
    if prior_tracked_gh_export(cmd):
        return (
            "review-gate: exported GH_HOST/GH_REPO/GH_CONFIG_DIR/XDG_CONFIG_HOME/HOME "
            "before `gh pr merge` (not modeled across segments); set them on the "
            "merge command itself (e.g. `GH_HOST=… gh -R owner/repo pr merge <n>`)"
        )
    # Prior `unset` / `declare +x` / `export -n` drops the var for the merge only.
    if prior_tracked_gh_unset(cmd):
        return (
            "review-gate: `unset`/`declare +x`/`export -n` of "
            "GH_HOST/GH_REPO/GH_CONFIG_DIR/XDG_CONFIG_HOME/HOME before `gh pr merge` "
            "(not mirrored into the gate); clear via `env -u … gh -R owner/repo pr merge <n>` "
            "on the merge command itself"
        )
    # `eval` / `source` / `.` / `trap` can hide merges the gate never inspects
    # (including traps installed *after* the validated merge segment).
    if shell_mutation_before_merge(cmd):
        return (
            "review-gate: `eval`/`source`/`.`/`trap`/`enable -f` with `gh pr merge` "
            "(can redefine `gh`, load a dynamic builtin, or run a merge from a trap); "
            "run literal `gh -R owner/repo pr merge <n>` without sourcing, eval, "
            "trap, or enable -f"
        )
    # Function/alias/hash named `gh` shadows the binary the gate inspects.
    if redefines_gh(cmd):
        return (
            "review-gate: `gh` function/alias/hash redefinition with `gh pr merge`; "
            "run the real `gh` binary without shadowing it"
        )
    # Wrappers stripped as "harmless" (`env`/`command`/…) can be shadowed functions.
    if redefines_prefix_builtin(cmd):
        return (
            "review-gate: `env`/`command`/`builtin`/`exec`/`time` redefinition with "
            "`gh pr merge`; run literal `gh -R owner/repo pr merge <n>` without "
            "shadowing those wrappers"
        )
    # Local `command_not_found_handle(){…}` with a loose `pr merge` shape.
    if defines_command_not_found_handle(cmd):
        return (
            "review-gate: local `command_not_found_handle` with `pr merge` "
            "(unresolved names like `gx` run the handler); unset -f "
            "`command_not_found_handle` and run literal "
            "`gh -R owner/repo pr merge <n>`"
        )
    # Inherited `export -f gh` / `command_not_found_handle` (BASH_FUNC_*%%).
    if inherited_shadowing_function(cmd):
        return (
            "review-gate: inherited Bash function shadows `gh`/`command`/`env`/… "
            "or `command_not_found_handle` (BASH_FUNC_*%%); unset -f those names "
            "before `gh -R owner/repo pr merge <n>`"
        )
    # Non-exported defs via BASH_ENV are invisible as BASH_FUNC_*%%.
    if inherited_bash_env(cmd):
        return (
            "review-gate: nonempty `BASH_ENV` with `gh pr merge` "
            "(non-interactive Bash sources it and can shadow `gh`); "
            "unset BASH_ENV before `gh -R owner/repo pr merge <n>`"
        )
    # `set -a` makes later assignments export into the merge child (e.g. GH_HOST).
    if allexport_before_merge(cmd):
        return (
            "review-gate: `set -a`/`set -o allexport` before `gh pr merge` "
            "(assignments become exports); set GH_* on the merge command itself"
        )
    # `set -k` puts trailing assignment args into the merge child's environment.
    if keyword_before_merge(cmd):
        return (
            "review-gate: `set -k`/`set -o keyword` before `gh pr merge` "
            "(trailing NAME=VALUE become env); set GH_* as a leading assign on the "
            "merge command itself"
        )
    # Nameref can retarget GH_HOST/… without a literal tracked-name assignment.
    if nameref_with_merge(cmd):
        return (
            "review-gate: `declare -n`/`typeset -n`/`local -n` with `gh pr merge` "
            "(can mutate GH_HOST/config via nameref); set GH_* on the merge command itself"
        )
    # Wrapped / substituted merges in ANY segment — even when another segment is
    # a literal direct merge (`echo $(gh … pr merge 2); gh -R safe pr merge 1`).
    # `is_gh_pr_merge` false means the merge is inside `$()` / quotes / eval text;
    # non-direct wrappers (`xargs`/`ssh`) still flow through `iter_merge_segments`.
    # Skip direct ``gh pr comment|view|…`` where ``merge`` is only flag/body data.
    if any(
        MERGE_RE.search(p) and not is_gh_pr_merge(p) and not _direct_gh_pr_non_merge(p)
        for p in parts
    ):
        return (
            "review-gate: shell-wrapped `gh pr merge` detected "
            "(e.g. `bash -c` / `eval` / `$(…)`); run `gh -R owner/repo pr merge <n>` directly"
        )
    # Nested `$(gh … pr merge)` inside the same segment as a direct merge.
    if any(nested_merge_in_segment(p) for p in parts):
        return (
            "review-gate: nested `$(gh pr merge)` / backtick merge beside a direct "
            "`gh pr merge`; run a single literal `gh -R owner/repo pr merge <n>`"
        )
    # `gh alias set …` / `gh sneak` can expand to an unchecked `pr merge`.
    if gh_alias_merge_risk(cmd) or any(gh_alias_merge_risk(p) for p in parts):
        return (
            "review-gate: `gh` alias configuration/opaque invocation "
            "(e.g. `gh alias set …` / `gh sneak`); run literal "
            "`gh -R owner/repo pr merge <n>` without aliases"
        )
    if not any(is_gh_pr_merge(p) for p in parts):
        return None
    start = cwd or os.getcwd()
    segments, seg_err = iter_merge_segments(cmd, start)
    if seg_err:
        return seg_err
    if not segments:
        if segment_has_override(cmd):
            return None
        if not gh_is_direct_command(cmd):
            return (
                "review-gate: `gh pr merge` must be the directly executed command "
                "(no ssh/xargs/docker/… wrappers); run `gh -R owner/repo pr merge <n>`"
            )
        if scoped_dir_requires_repo(cmd) and not has_literal_repo(cmd):
            return (
                "review-gate: command-scoped directory change detected "
                "(e.g. `env -C`/`--chdir` / subshell `cd`); pass `-R owner/repo` explicitly"
            )
        if sets_git_location(cmd) and not has_literal_repo(cmd):
            return (
                "review-gate: GIT_DIR/GIT_CONFIG_* without literal `-R owner/repo`; "
                "pass `-R` (git location/config env is not modeled)"
            )
        return check_one(cmd, start)
    for segment, seg_cwd in segments:
        if segment_has_override(segment):
            continue
        err = check_one(segment, seg_cwd)
        if err:
            return err
    return None


def main() -> int:
    # Any tool the hook matcher routes here is checked when it carries a command, whatever the harness
    # names it (`Bash`, `mcp__…__Bash`, `run_shell_command`): an allow-list of tool names failed open.
    # Unreadable input blocks: a guard that cannot see the command must not let it through.
    try:
        payload = json.load(sys.stdin)
        inp = payload.get("tool_input") or payload.get("input") or {}
        cmd = inp.get("command") or inp.get("cmd") or ""
    except (ValueError, AttributeError) as exc:
        print(f"review-gate merge guard: unreadable hook input ({type(exc).__name__}); blocked", file=sys.stderr)
        return 2
    if not isinstance(cmd, str) or not cmd:
        return 0
    cwd = payload_cwd(payload, inp)
    err = check_command(cmd, cwd)
    if err:
        print(err, file=sys.stderr)
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
    # Fail closed on ANY crash: a PreToolUse hook exiting 1 is a non-blocking error, so the command would
    # run. A ~1000-deep `$( … )` nest raised RecursionError and exited 1 (Sonnet pass on 07baddd).
    try:
        rc = main()
    except BaseException as exc:  # noqa: BLE001 - only exit 2 blocks the tool call
        rc = 2
        print(f"review-gate merge guard: crashed ({type(exc).__name__}); blocked", file=sys.stderr)
        try:
            fb_log("hook:review-gate/rg-merge-guard", "high", f"merge-guard crashed: {type(exc).__name__}")
        except Exception as log_exc:  # noqa: BLE001 - logging must not turn the block into exit 1
            print(f"review-gate merge guard: feedback log failed ({type(log_exc).__name__})", file=sys.stderr)
    sys.exit(rc)
