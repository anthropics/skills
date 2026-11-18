#!/usr/bin/env python3
"""Deterministic review-gate checks shared by CI and the PreToolUse merge guard.

Exit 0 = pass. Exit 1 = fail (print reasons on stdout). Exit 2 = usage / infra error.
"""
from __future__ import annotations

import contextlib
import json
import os
import re
import subprocess
import sys
from contextvars import ContextVar
from typing import Any, Iterator

# Optional env for gate ``gh`` subprocesses (merge-guard command-scoped GH_*).
_GH_SUBPROCESS_ENV: ContextVar[dict[str, str] | None] = ContextVar(
    "review_gate_gh_env", default=None
)

P2_ROOT = re.compile(r"(?<![A-Za-z0-9])p2(?![A-Za-z0-9])", re.I | re.A)  # _P2_ and P2_x count
# A P2 thread closes on a reply whose FIRST line is, from column 0 to its end, exactly one closing token
# and is the whole first paragraph: the reply ends there or the next line is blank (only spaces/tabs, as
# in CommonMark). Nothing precedes that line, so no fence, quote, list, comment or HTML block can enclose
# it, and nothing directly after it can turn it into a setext heading or a table header. Nothing may
# follow a SHA or a Notion link on that line ("fixed in 0123456 - not really" does not close). A Notion
# link needs link text starting with a letter or digit. Anything else does not close. No Markdown is parsed.
_NOTION_URL = r"https?://(?:[a-z0-9-]+\.)?notion\.(?:so|com)/[A-Za-z0-9][^\s<>()\[\]`]*"
_CLOSING_TOKEN = re.compile(
    r"(?:tracked:?[ \t]+)?"
    rf"(?:\[[A-Za-z0-9][^\[\]<>\n]*\]\({_NOTION_URL}\)|<{_NOTION_URL}>|{_NOTION_URL}"
    r"|fixed in (?:commit )?(`?)[0-9a-f]{7,40}\1|not-a-finding:[ \t]*[A-Za-z0-9].*)[ \t.]*",
    re.I | re.A,
)


CLOSER_ASSOCIATIONS = frozenset({"OWNER", "MEMBER", "COLLABORATOR"})
# Repo roles that also close, read from the legacy `permission` field (maintain reads as write, triage as read).
CLOSER_PERMISSIONS = frozenset({"admin", "write"})
_GITHUB_LOGIN = re.compile(r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})", re.A)


def closes(reply: str) -> bool:
    """True when the reply's first line is exactly one closing token and stands alone."""
    lines = reply.replace("\r\n", "\n").replace("\r", "\n").split("\n", 2)
    if len(lines) > 1 and not _is_blank(lines[1]):
        return False
    return bool(_CLOSING_TOKEN.fullmatch(lines[0]))


def _is_blank(line: str) -> bool:
    """CommonMark blank: only spaces and tabs. str.strip() would also drop NBSP, U+2028, form feed, ..."""
    return not line.strip(" \t")


FALLBACK_ATTESTATION = re.compile(
    r"Fallback review: (codex|agy|antigravity|superpowers|claude-sonnet) on "
    r"([0-9a-f]{40}) — verdict: (clean|findings fixed)",
    re.I | re.A,
)
MAIN_REVIEW_LABELS = {"review:high"}
# Exact bot logins only — substring matches like "codex-helper" must not pass the gate.
CODEX_AUTHORS = frozenset({"chatgpt-codex-connector"})
# A clean Codex run posts no review, only this state marker in its summary PR comment.
CODEX_STATE = re.compile(r"<!-- codex-review-state:v1 (\{.*?\}) -->", re.S)


DOTCOM_HOSTS = frozenset({"github.com", "www.github.com"})


@contextlib.contextmanager
def gh_subprocess_env(env: dict[str, str] | None) -> Iterator[None]:
    """Apply a temporary env to every ``gh`` subprocess in this context."""
    token = _GH_SUBPROCESS_ENV.set(env)
    try:
        yield
    finally:
        _GH_SUBPROCESS_ENV.reset(token)


def _describe_call(args: list[str]) -> str:
    """'<METHOD> <endpoint>' for an error message; field values (queries, bodies) are left out.
    Like gh, the method defaults to POST when fields are passed and no -X/--method is given."""
    method, endpoint, fields, i = None, "", False, 0
    while i < len(args):
        a = args[i]
        if a in ("-X", "--method"):
            method = args[i + 1] if i + 1 < len(args) else None
            i += 2
        elif a in ("-f", "-F", "--field", "--raw-field"):
            fields, i = True, i + 2
        elif a in ("-H", "--header", "--jq", "-q", "--hostname", "-R"):
            i += 2
        else:
            if not a.startswith("-") and not endpoint:
                endpoint = a
            i += 1
    return f"{method or ('POST' if fields else 'GET')} {endpoint or '?'}"


def run_gh(
    args: list[str],
    repo: str | None = None,
    hostname: str | None = None,
) -> Any:
    """Run `gh api`, optionally targeting an Enterprise host."""
    cmd = ["gh", "api"]
    if hostname:
        cmd.extend(["--hostname", hostname])
    if repo:
        cmd.extend(["-R", repo])
    cmd.extend(args)
    proc = subprocess.run(
        cmd, capture_output=True, text=True, env=_GH_SUBPROCESS_ENV.get()
    )
    if proc.returncode != 0:
        detail = proc.stderr.strip() or proc.stdout.strip() or "no output"
        raise RuntimeError(f"gh api {_describe_call(args)} failed (exit {proc.returncode}): {detail}")
    if not proc.stdout.strip():
        return None
    return json.loads(proc.stdout)


def _normalize_api_hostname(host: str | None) -> str | None:
    """Normalize a hostname for ``gh api --hostname``.

    Keep ``github.com`` explicit so a process-level Enterprise ``GH_HOST`` cannot
    redirect hostless/default API calls away from an intentional dotcom target.
    """
    if not host:
        return None
    if host.lower() in DOTCOM_HOSTS:
        return "github.com"
    return host


def parse_repo_with_host(
    repo: str | None,
    cwd: str | None = None,
    env: dict[str, str] | None = None,
) -> tuple[str | None, str, str]:
    """Resolve (hostname|None, owner, name).

    Accepts gh's `[HOST/]OWNER/REPO` form. Explicit ``github.com`` is retained
    (as ``github.com``) so ``--hostname`` overrides an inherited Enterprise
    ``GH_HOST``. Other Enterprise hosts are preserved as-is.

    ``env`` is passed to ``gh repo view`` when resolving from cwd (used to scrub
    a process-level ``GH_REPO`` the merge command cleared).
    """
    if repo and "/" in repo:
        parts = [p for p in repo.strip().strip("/").split("/") if p]
        if len(parts) >= 2:
            owner, name = parts[-2], parts[-1]
            if name.endswith(".git"):
                name = name[: -len(".git")]
            host: str | None = None
            if len(parts) >= 3:
                host = _normalize_api_hostname(parts[0])
            return host, owner, name
    view_cmd = [
        "gh",
        "repo",
        "view",
        "--json",
        "owner,name,url",
        "-q",
        ".owner.login + \"/\" + .name + \" \" + .url",
    ]
    proc = subprocess.run(
        view_cmd,
        capture_output=True,
        text=True,
        cwd=cwd or None,
        env=env,
    )
    if proc.returncode != 0 or "/" not in proc.stdout:
        raise RuntimeError("could not resolve owner/repo; pass --repo OWNER/NAME")
    slug_and_url = proc.stdout.strip().split(None, 1)
    slug = slug_and_url[0]
    owner, name = slug.split("/", 1)
    host = None
    if len(slug_and_url) > 1:
        m = re.match(r"https?://([^/]+)/", slug_and_url[1], re.I)
        if m:
            # Dotcom URLs stay explicit so inherited GH_HOST cannot hijack queries.
            host = _normalize_api_hostname(m.group(1))
    return host, owner, name


def parse_repo(repo: str | None, cwd: str | None = None) -> tuple[str, str]:
    """Resolve OWNER/NAME. Prefer an explicit --repo; else `gh repo view` in cwd."""
    _host, owner, name = parse_repo_with_host(repo, cwd=cwd)
    return owner, name


def is_codex_author(login: str | None) -> bool:
    """True only for the known Codex GitHub App login — never body text or substrings."""
    return (login or "").lower() in CODEX_AUTHORS


def _graphql(
    query: str, hostname: str | None = None, **variables: Any
) -> dict[str, Any]:
    args = ["graphql", "-f", f"query={query}"]
    for key, value in variables.items():
        args.extend(["-F", f"{key}={value}"])
    data = run_gh(args, hostname=hostname)
    return (data or {}).get("data") or {}  # an empty result fails closed in _all_nodes / pr_payload


_COMMENT_FIELDS = "pageInfo { hasNextPage endCursor } nodes { body author { __typename login } authorAssociation }"
_PR_CONNECTION_Q = """
query($owner:String!, $name:String!, $number:Int!, $cursor:String) {
  repository(owner:$owner, name:$name) {
    pullRequest(number:$number) {
      %s(first: 50, after: $cursor) { pageInfo { hasNextPage endCursor } nodes { %s } }
    }
  }
}
"""
_THREAD_COMMENTS_Q = """
query($id:ID!, $cursor:String) {
  node(id: $id) { ... on PullRequestReviewThread { comments(first: 50, after: $cursor) { %s } } }
}
""" % _COMMENT_FIELDS


def _all_nodes(conn: Any, what: str, next_page: Any) -> list[dict[str, Any]]:
    """Every node of a GraphQL connection, fetching later pages with next_page(cursor).

    Fails closed: a missing connection, or a next page with no cursor, raises instead of
    reading as an empty (passing) list."""
    nodes: list[dict[str, Any]] = []
    while True:
        if not isinstance(conn, dict):
            raise RuntimeError(f"GraphQL returned no {what}")
        nodes.extend(conn.get("nodes") or [])
        page = conn.get("pageInfo") or {}
        if not page.get("hasNextPage"):
            return nodes
        if not page.get("endCursor"):
            raise RuntimeError(f"GraphQL {what}: next page without a cursor")
        conn = next_page(page["endCursor"])


def _pr_connection(
    owner: str, name: str, number: int, field: str, fields: str, hostname: str | None = None
) -> list[dict[str, Any]]:
    """Every node of pullRequest.<field> (reviews, labels, comments, reviewThreads)."""
    q = _PR_CONNECTION_Q % (field, fields)

    def fetch(cursor: str | None) -> Any:
        variables: dict[str, Any] = {"owner": owner, "name": name, "number": number}
        if cursor:
            variables["cursor"] = cursor
        data = _graphql(q, hostname=hostname, **variables)
        return ((data.get("repository") or {}).get("pullRequest") or {}).get(field)

    return _all_nodes(fetch(None), f"pullRequest.{field} for {owner}/{name}#{number}", fetch)


def _review_threads(owner: str, name: str, number: int, hostname: str | None = None) -> list[dict[str, Any]]:
    """Every review thread with every comment; comments past the first 50 are fetched per thread."""
    threads = []
    for node in _pr_connection(owner, name, number, "reviewThreads",
                               f"id comments(first: 50) {{ {_COMMENT_FIELDS} }}", hostname):
        thread_id = node.get("id")

        def more(cursor: str, _id: Any = thread_id) -> Any:
            data = _graphql(_THREAD_COMMENTS_Q, hostname=hostname, id=_id, cursor=cursor)
            return (data.get("node") or {}).get("comments")

        comments = _all_nodes(node.get("comments"), f"comments of review thread {thread_id}", more)
        threads.append({"comments": {"nodes": comments}})
    return threads


def codex_clean_comment_on_head(pr: dict[str, Any]) -> bool:
    """True when Codex's summary comment says a code review completed on the
    current head with no unresolved findings (the clean case posts no review)."""
    head = pr.get("headRefOid") or ""
    if not head:
        return False
    for c in pr.get("comments", {}).get("nodes") or []:
        if not is_codex_author((c.get("author") or {}).get("login")):
            continue
        # every marker in the comment, not only the first one
        for m in CODEX_STATE.finditer(c.get("body") or ""):
            try:
                review = json.loads(m.group(1)).get("code_review") or {}
            except (ValueError, AttributeError):
                continue  # malformed marker: not evidence of a review; fail closed
            if (
                review.get("commit_sha") == head
                and review.get("status") == "completed"
                and review.get("has_unresolved_findings") is False
            ):
                return True
    return False


def pr_payload(
    owner: str, name: str, number: int, hostname: str | None = None
) -> dict[str, Any]:
    q = """
    query($owner:String!, $name:String!, $number:Int!) {
      repository(owner:$owner, name:$name) {
        pullRequest(number:$number) {
          number
          body
          baseRefName
          headRefOid
        }
      }
    }
    """
    data = _graphql(q, hostname=hostname, owner=owner, name=name, number=number)
    pr = (data.get("repository") or {}).get("pullRequest")
    if not pr:
        raise RuntimeError(f"PR #{number} not found in {owner}/{name}")
    pr["labels"] = {"nodes": _pr_connection(owner, name, number, "labels", "name", hostname)}
    pr["reviews"] = {"nodes": _pr_connection(owner, name, number, "reviews",
                                             "state body commit { oid } author { login }", hostname)}
    # Codex keeps one summary comment updated: every PR conversation comment is read.
    pr["comments"] = {"nodes": _pr_connection(owner, name, number, "comments", "author { login } body", hostname)}
    pr["reviewThreads"] = {"nodes": _review_threads(owner, name, number, hostname)}
    pr["closerPermissions"] = closer_permissions(owner, name, pr, hostname)
    return pr


def closer_permissions(
    owner: str, name: str, pr: dict[str, Any], hostname: str | None = None
) -> dict[str, str]:
    """Repo permission of each user whose closing reply to a P2 thread lacks a closer association.

    The Actions GITHUB_TOKEN cannot see private org membership, so it reads a private member's reply as
    CONTRIBUTOR where a user token reads MEMBER (review-gate-sandbox run 44388630509; nevar-fund #27).
    The collaborator permission endpoint reads the repo role directly. Only `User` authors are looked up,
    so bots never close by this path. Any API error raises, naming the call: the gate fails closed."""
    perms: dict[str, str] = {}
    for _, replies in _p2_threads(pr):
        for c in replies:
            author = c.get("author") or {}
            login = author.get("login") or ""
            if (author.get("__typename") != "User" or login in perms or not _GITHUB_LOGIN.fullmatch(login)
                    or c.get("authorAssociation") in CLOSER_ASSOCIATIONS or not closes(c.get("body") or "")):
                continue
            endpoint = f"repos/{owner}/{name}/collaborators/{login}/permission"
            data = run_gh([endpoint], hostname=hostname)
            perm = data.get("permission") if isinstance(data, dict) else None
            if not isinstance(perm, str):
                raise RuntimeError(f"gh api GET {endpoint} returned no permission")
            perms[login] = perm
    return perms


def codex_done_on_head(pr: dict[str, Any]) -> bool:
    """True when a non-pending Codex review exists on the current head OID.

    Fail closed when ``commit.oid`` is missing (e.g. reviewed commit deleted) —
    an empty commit must not satisfy the current head.
    """
    head = pr.get("headRefOid") or ""
    if not head:
        return False
    for rev in pr.get("reviews", {}).get("nodes") or []:
        commit = (rev.get("commit") or {}).get("oid") or ""
        if not commit or commit != head:
            continue
        author = ((rev.get("author") or {}).get("login") or "")
        if not is_codex_author(author):
            continue
        state = (rev.get("state") or "").upper()
        if state in ("PENDING", "DISMISSED"):
            continue
        body = rev.get("body") or ""
        if "running" in body.lower() and len(body) < 400:
            continue
        return True
    return False


# PR-body grammar (Program 19:10 directive, #105): a strict allow-list over physical lines, with no
# Markdown parsing and no recovery. Anything outside it fails the whole check with a reason naming the
# line, so the author rewrites the body instead of the gate guessing what GitHub renders.
_FENCE_LINE = re.compile(r"[ \t]*(?:`{3}|~{3})")
# A line whose first character after quote/list markers is `<` can open an HTML block, and an unterminated
# attribute (`<div title='`) or a type 1-5 block (`<pre>`, `<!`, `<?`) swallows the lines after it,
# `## Review` included, so every such line is banned. A comment is banned anywhere; `<details` too, since
# an unclosed one collapses what follows even mid-line.
_DETAILS_TAG = re.compile(r"<details(?![A-Za-z0-9-])", re.I)
_RAW_HTML_LINE = re.compile(r"[ \t>*+\-0-9.)]*<")
REVIEW_HEADING = "## Review"
_PROSE_LINE = re.compile(r"[A-Za-z0-9][^`<>|\[\]()*_~$]*")
_ORDERED_MARKER = re.compile(r"[0-9]{1,9}[.)](?:[ \t]|$)")


def review_region(body: str) -> tuple[list[str], list[str]]:
    """Return (region lines, problems) for the PR body's single `## Review` section.

    Whole body: no ``` or ~~~ line, no `<!--`, no `<details`, no line whose first character after quote/list markers is `<`. Exactly one
    line equal to `## Review`, after a blank line or at the top. The region runs to the next line
    starting `## ` or the end. Every non-blank region line is plain prose: starts with a letter or
    digit, no ordered-list marker, and none of ` < > | [ ] ( ) * _ ~ $ (an attestation or closing line
    is such prose). Blank means only spaces and tabs. Any other line fails the check.
    """
    lines = body.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    problems: list[str] = []
    for n, line in enumerate(lines, 1):
        if _FENCE_LINE.match(line):
            problems.append(f"PR body line {n}: code fences (``` or ~~~) are not allowed in a gated PR body")
        if "<!--" in line:
            problems.append(f"PR body line {n}: HTML comments (<!--) are not allowed in a gated PR body")
        elif _RAW_HTML_LINE.match(line):
            problems.append(f"PR body line {n}: a line starting with < (raw HTML) is not allowed in a gated PR body")
        if _DETAILS_TAG.search(line):
            problems.append(f"PR body line {n}: <details> is not allowed in a gated PR body (an unclosed one collapses ## Review)")
    headings = [i for i, line in enumerate(lines) if line.rstrip() == REVIEW_HEADING]
    if len(headings) != 1:
        problems.append(f"PR body must have exactly one line '{REVIEW_HEADING}' (found {len(headings)})")
        return [], problems
    start = headings[0]
    if start and not _is_blank(lines[start - 1]):
        problems.append(f"PR body line {start + 1}: '{REVIEW_HEADING}' must follow a blank line")
    region: list[str] = []
    for n, line in enumerate(lines[start + 1 :], start + 2):
        if line.startswith("## "):
            break
        region.append(line)
        if _is_blank(line) or (_PROSE_LINE.fullmatch(line) and not _ORDERED_MARKER.match(line)):
            continue
        problems.append(
            f"PR body line {n}: in ## Review every line must be plain prose (starting with a letter or "
            "digit, no list marker, none of ` < > | [ ] ( ) * _ ~ $)"
        )
    return region, problems


def review_section_names_fallback(body: str, head: str | None = None) -> bool:
    """True when the well-formed ## Review region holds an exact attestation for the current head.

    The whole line must equal the attestation (no extra text) and name the full 40-hex head OID: a short
    prefix could be ground onto an unreviewed commit.
    """
    if not head:
        return False
    region, problems = review_region(body)
    if problems:
        return False
    for line in region:
        attestation = FALLBACK_ATTESTATION.fullmatch(line)
        if attestation and head.lower() == attestation.group(2).lower():
            return True
    return False


def _p2_threads(pr: dict[str, Any]) -> Iterator[tuple[int, list[dict[str, Any]]]]:
    """(1-based thread index, replies) for every review thread whose root comment is a P2."""
    for i, thread in enumerate(pr.get("reviewThreads", {}).get("nodes") or [], 1):
        comments = thread.get("comments", {}).get("nodes") or []
        if comments and P2_ROOT.search(comments[0].get("body") or ""):
            yield i, comments[1:]


def p2_threads_closed(pr: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    perms = pr.get("closerPermissions") or {}

    def may_close(c: dict[str, Any]) -> bool:
        # Only an owner, org member, collaborator, or a user with write/admin on the repo closes: on a
        # public repo anyone can reply to a thread. The permission covers private org members, whom the
        # Actions token sees as CONTRIBUTOR (closer_permissions). The PR author may close: every agent and
        # reviewer here shares one gh login with the author (claude-skills #105: all 15 human replies are
        # the author's), so barring the author would leave every P2 unclosable. Binding closers to a
        # separate reviewer identity is plan PR #113 (gate step 3), which replaces both paths.
        if c.get("authorAssociation") in CLOSER_ASSOCIATIONS:
            return True
        author = c.get("author") or {}
        return author.get("__typename") == "User" and perms.get(author.get("login")) in CLOSER_PERMISSIONS

    for i, replies in _p2_threads(pr):
        closing = [c for c in replies if closes(c.get("body") or "")]
        if any(may_close(c) for c in closing):
            continue
        not_counted = sorted({
            f"{(c.get('author') or {}).get('login') or '?'} ({c.get('authorAssociation') or '?'}, "
            f"permission {perms.get((c.get('author') or {}).get('login'), 'not looked up')})"
            for c in closing
        })
        failures.append(
            f"P2 thread #{i} has no closing reply from a repo owner, member, collaborator or user with write access "
            "(Notion link / fixed in <sha> / not-a-finding:)"
            + (f"; closing replies not counted: {', '.join(not_counted)}" if not_counted else "")
        )
    return failures


def evaluate(pr: dict[str, Any]) -> list[str]:
    reasons: list[str] = []
    body = pr.get("body") or ""
    head = pr.get("headRefOid") or ""
    reasons.extend(review_region(body)[1])
    if not (
        codex_done_on_head(pr)
        or codex_clean_comment_on_head(pr)
        or review_section_names_fallback(body, head)
    ):
        reasons.append(
            "No completed Codex review on current head, and ## Review lacks a completed "
            "fallback attestation: Fallback review: <codex|agy|antigravity|superpowers|claude-sonnet> "
            "on <head SHA> — verdict: <clean|findings fixed>"
        )
    reasons.extend(p2_threads_closed(pr))
    if (pr.get("baseRefName") or "") == "main":
        labels = {n.get("name") for n in (pr.get("labels", {}).get("nodes") or [])}
        if not (labels & MAIN_REVIEW_LABELS):
            reasons.append("base is main but label review:high is missing")
    return reasons


def main(argv: list[str]) -> int:
    repo = None
    number = None
    i = 0
    while i < len(argv):
        if argv[i] in ("--repo", "-R") and i + 1 < len(argv):
            repo = argv[i + 1]
            i += 2
        elif argv[i] in ("--pr", "-p") and i + 1 < len(argv):
            number = int(argv[i + 1])
            i += 2
        elif argv[i].isdigit() and number is None:
            number = int(argv[i])
            i += 1
        else:
            print("usage: check_review_gate.py --pr N [--repo OWNER/NAME]", file=sys.stderr)
            return 2
    if number is None:
        env_n = os.environ.get("PR_NUMBER") or os.environ.get("GITHUB_PR_NUMBER")
        if env_n:
            number = int(env_n)
    if number is None:
        print("usage: check_review_gate.py --pr N [--repo OWNER/NAME]", file=sys.stderr)
        return 2
    try:
        hostname, owner, name = parse_repo_with_host(repo)
        pr = pr_payload(owner, name, number, hostname=hostname)
        reasons = evaluate(pr)
    except Exception as e:  # noqa: BLE001 — surface to CI/agent
        print(str(e), file=sys.stderr)
        return 2
    if reasons:
        print("review-gate failed:")
        for r in reasons:
            print(f"- {r}")
        return 1
    print("review-gate ok")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
