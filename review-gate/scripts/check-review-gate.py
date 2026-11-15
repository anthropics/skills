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

P2_ROOT = re.compile(r"\bp2\b", re.I)
CLOSING = re.compile(
    r"notion\.(so|com)/|fixed in (commit )?`?[0-9a-f]{7,40}`?|not-a-finding:\s*\S",
    re.I,
)
FALLBACK_ATTESTATION = re.compile(
    r"Fallback review: (agy|antigravity|superpowers|claude-sonnet) on "
    r"([0-9a-f]{7,40}) — verdict: (clean|findings fixed)",
    re.I,
)
INCOMPLETE_REVIEW = re.compile(r"\b(pending|running|todo)\b", re.I)
REVIEW_SECTION = re.compile(r"(?m)^##\s+Review\b")
MAIN_REVIEW_LABELS = {"review:high"}
# Exact bot logins only — substring matches like "codex-helper" must not pass the gate.
CODEX_AUTHORS = frozenset({"chatgpt-codex-connector"})


DOTCOM_HOSTS = frozenset({"github.com", "www.github.com"})


@contextlib.contextmanager
def gh_subprocess_env(env: dict[str, str] | None) -> Iterator[None]:
    """Apply a temporary env to every ``gh`` subprocess in this context."""
    token = _GH_SUBPROCESS_ENV.set(env)
    try:
        yield
    finally:
        _GH_SUBPROCESS_ENV.reset(token)


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
        raise RuntimeError(proc.stderr.strip() or proc.stdout.strip() or "gh api failed")
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
    return (data or {}).get("data") or {}


def _paginate_thread_comments(
    thread_id: str,
    hostname: str | None,
    first_page: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    """Return all comments for a thread, starting from an optional embedded page."""
    comments: list[dict[str, Any]] = []
    c_conn = first_page or {}
    if first_page is not None:
        comments.extend(first_page.get("nodes") or [])
        page = first_page.get("pageInfo") or {}
        if not page.get("hasNextPage"):
            return comments
        c_cursor = page.get("endCursor")
        if not c_cursor:
            return comments
    else:
        c_cursor = None

    comment_q = """
    query($id:ID!, $cursor:String) {
      node(id: $id) {
        ... on PullRequestReviewThread {
          comments(first: 50, after: $cursor) {
            pageInfo { hasNextPage endCursor }
            nodes { body author { login } }
          }
        }
      }
    }
    """
    comment_first = """
    query($id:ID!) {
      node(id: $id) {
        ... on PullRequestReviewThread {
          comments(first: 50) {
            pageInfo { hasNextPage endCursor }
            nodes { body author { login } }
          }
        }
      }
    }
    """
    while True:
        if c_cursor is None:
            c_conn = (
                _graphql(comment_first, hostname=hostname, id=thread_id).get("node") or {}
            ).get("comments") or {}
            comments.extend(c_conn.get("nodes") or [])
        else:
            c_conn = (
                _graphql(
                    comment_q, hostname=hostname, id=thread_id, cursor=c_cursor
                ).get("node")
                or {}
            ).get("comments") or {}
            comments.extend(c_conn.get("nodes") or [])
        page = c_conn.get("pageInfo") or {}
        if not page.get("hasNextPage"):
            break
        c_cursor = page.get("endCursor")
        if not c_cursor:
            break
    return comments


def _paginate_threads(owner: str, name: str, number: int, hostname: str | None = None) -> list[dict[str, Any]]:
    """Fetch every review thread with comments embedded in the thread query.

    Most threads fit in the first comments page (50), so one GraphQL call covers
    up to 50 threads. Extra comment pages are fetched only when ``hasNextPage``.
    """
    threads: list[dict[str, Any]] = []
    cursor: str | None = None
    thread_q = """
    query($owner:String!, $name:String!, $number:Int!, $cursor:String) {
      repository(owner:$owner, name:$name) {
        pullRequest(number:$number) {
          reviewThreads(first: 50, after: $cursor) {
            pageInfo { hasNextPage endCursor }
            nodes {
              id
              comments(first: 50) {
                pageInfo { hasNextPage endCursor }
                nodes { body author { login } }
              }
            }
          }
        }
      }
    }
    """
    while True:
        if cursor is None:
            first_q = """
            query($owner:String!, $name:String!, $number:Int!) {
              repository(owner:$owner, name:$name) {
                pullRequest(number:$number) {
                  reviewThreads(first: 50) {
                    pageInfo { hasNextPage endCursor }
                    nodes {
                      id
                      comments(first: 50) {
                        pageInfo { hasNextPage endCursor }
                        nodes { body author { login } }
                      }
                    }
                  }
                }
              }
            }
            """
            conn = (
                _graphql(first_q, hostname=hostname, owner=owner, name=name, number=number)
                .get("repository", {})
                .get("pullRequest", {})
                .get("reviewThreads")
                or {}
            )
        else:
            conn = (
                _graphql(
                    thread_q,
                    hostname=hostname,
                    owner=owner,
                    name=name,
                    number=number,
                    cursor=cursor,
                )
                .get("repository", {})
                .get("pullRequest", {})
                .get("reviewThreads")
                or {}
            )
        for node in conn.get("nodes") or []:
            thread_id = node.get("id")
            if not thread_id:
                continue
            embedded = node.get("comments") or {}
            comments = _paginate_thread_comments(
                thread_id, hostname, first_page=embedded
            )
            threads.append({"comments": {"nodes": comments}})
        page = conn.get("pageInfo") or {}
        if not page.get("hasNextPage"):
            break
        cursor = page.get("endCursor")
        if not cursor:
            break
    return threads


def _paginate_reviews(owner: str, name: str, number: int, hostname: str | None = None) -> list[dict[str, Any]]:
    """Fetch every submitted review (not just the last 40)."""
    reviews: list[dict[str, Any]] = []
    cursor: str | None = None
    while True:
        if cursor is None:
            q = """
            query($owner:String!, $name:String!, $number:Int!) {
              repository(owner:$owner, name:$name) {
                pullRequest(number:$number) {
                  reviews(first: 50) {
                    pageInfo { hasNextPage endCursor }
                    nodes {
                      state
                      body
                      commit { oid }
                      author { login }
                    }
                  }
                }
              }
            }
            """
            conn = (
                _graphql(q, hostname=hostname, owner=owner, name=name, number=number)
                .get("repository", {})
                .get("pullRequest", {})
                .get("reviews")
                or {}
            )
        else:
            q = """
            query($owner:String!, $name:String!, $number:Int!, $cursor:String!) {
              repository(owner:$owner, name:$name) {
                pullRequest(number:$number) {
                  reviews(first: 50, after: $cursor) {
                    pageInfo { hasNextPage endCursor }
                    nodes {
                      state
                      body
                      commit { oid }
                      author { login }
                    }
                  }
                }
              }
            }
            """
            conn = (
                _graphql(q, hostname=hostname, owner=owner, name=name, number=number, cursor=cursor)
                .get("repository", {})
                .get("pullRequest", {})
                .get("reviews")
                or {}
            )
        reviews.extend(conn.get("nodes") or [])
        page = conn.get("pageInfo") or {}
        if not page.get("hasNextPage"):
            break
        cursor = page.get("endCursor")
        if not cursor:
            break
    return reviews


def _paginate_labels(owner: str, name: str, number: int, hostname: str | None = None) -> list[dict[str, Any]]:
    """Fetch every label on the PR."""
    labels: list[dict[str, Any]] = []
    cursor: str | None = None
    while True:
        if cursor is None:
            q = """
            query($owner:String!, $name:String!, $number:Int!) {
              repository(owner:$owner, name:$name) {
                pullRequest(number:$number) {
                  labels(first: 50) {
                    pageInfo { hasNextPage endCursor }
                    nodes { name }
                  }
                }
              }
            }
            """
            conn = (
                _graphql(q, hostname=hostname, owner=owner, name=name, number=number)
                .get("repository", {})
                .get("pullRequest", {})
                .get("labels")
                or {}
            )
        else:
            q = """
            query($owner:String!, $name:String!, $number:Int!, $cursor:String!) {
              repository(owner:$owner, name:$name) {
                pullRequest(number:$number) {
                  labels(first: 50, after: $cursor) {
                    pageInfo { hasNextPage endCursor }
                    nodes { name }
                  }
                }
              }
            }
            """
            conn = (
                _graphql(q, hostname=hostname, owner=owner, name=name, number=number, cursor=cursor)
                .get("repository", {})
                .get("pullRequest", {})
                .get("labels")
                or {}
            )
        labels.extend(conn.get("nodes") or [])
        page = conn.get("pageInfo") or {}
        if not page.get("hasNextPage"):
            break
        cursor = page.get("endCursor")
        if not cursor:
            break
    return labels


def _paginate_issue_comments(
    owner: str, name: str, number: int, hostname: str | None = None
) -> list[dict[str, Any]]:
    """Fetch every PR conversation comment (Codex posts clean results here)."""
    out: list[dict[str, Any]] = []
    cursor: str | None = None
    q = """
    query($owner:String!, $name:String!, $number:Int!, $cursor:String) {
      repository(owner:$owner, name:$name) {
        pullRequest(number:$number) {
          comments(first: 100, after: $cursor) {
            pageInfo { hasNextPage endCursor }
            nodes { body author { login } }
          }
        }
      }
    }
    """
    while True:
        variables: dict[str, Any] = {"owner": owner, "name": name, "number": number}
        if cursor:
            variables["cursor"] = cursor
        conn = (
            _graphql(q, hostname=hostname, **variables)
            .get("repository", {})
            .get("pullRequest", {})
            .get("comments")
            or {}
        )
        out.extend(conn.get("nodes") or [])
        page = conn.get("pageInfo") or {}
        cursor = page.get("endCursor")
        if not page.get("hasNextPage") or not cursor:
            return out


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
    pr["labels"] = {"nodes": _paginate_labels(owner, name, number, hostname=hostname)}
    pr["reviews"] = {"nodes": _paginate_reviews(owner, name, number, hostname=hostname)}
    pr["issueComments"] = {
        "nodes": _paginate_issue_comments(owner, name, number, hostname=hostname)
    }
    pr["reviewThreads"] = {
        "nodes": _paginate_threads(owner, name, number, hostname=hostname)
    }
    return pr


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
    return any(
        _codex_comment_done_on(c, head)
        for c in (pr.get("issueComments") or {}).get("nodes") or []
    )


CODEX_STATE = re.compile(r"<!--\s*codex-review-state:v1\s*(\{.*?\})\s*-->", re.S)
CODEX_REVIEWED_COMMIT = re.compile(r"\*\*Reviewed commit:\*\*\s*`([0-9a-fA-F]{7,40})`")


def _codex_comment_done_on(comment: dict[str, Any], head: str) -> bool:
    """A Codex conversation comment reporting a finished review of ``head``.

    Clean results arrive as an issue comment, not a PullRequestReview. Accept
    the structured state marker (full-SHA match, status completed) or a
    ``Reviewed commit:`` line whose SHA is a prefix of head. "Running" never counts.
    """
    if not is_codex_author((comment.get("author") or {}).get("login")):
        return False
    body = comment.get("body") or ""
    m = CODEX_STATE.search(body)
    if m:
        try:
            cr = (json.loads(m.group(1)).get("code_review") or {})
        except ValueError:
            return False
        return cr.get("commit_sha") == head and cr.get("status") == "completed"
    m = CODEX_REVIEWED_COMMIT.search(body)
    if not m or not head.startswith(m.group(1).lower()):
        return False
    # The "About Codex" footer says "while any review is running" on every
    # comment, so strip it before looking for a Running status.
    status = re.sub(r"<details>\s*<summary>\s*ℹ️.*?</details>", "", body, flags=re.S)
    return "running" not in status.lower()


def _rendered_markdown(body: str) -> str:
    """Drop what GitHub does not render as prose: HTML comments, <pre>, code.

    An attestation shown as an example (comment, fence, indented code) must not
    count. Unclosed comments and fences run to the end of the body, as GitHub
    renders them, so this only ever removes more, never less.
    """
    text = body.replace("\r\n", "\n")
    text = re.sub(r"<!--.*?(?:-->|\Z)", "", text, flags=re.S)
    text = re.sub(r"<pre\b.*?(?:</pre\s*>|\Z)", "", text, flags=re.S | re.I)
    kept: list[str] = []
    fence: str | None = None
    for line in text.split("\n"):
        marker = re.match(r" {0,3}(`{3,}|~{3,})", line)
        if fence is not None:
            if marker and marker.group(1)[0] == fence[0] and len(marker.group(1)) >= len(fence):
                fence = None
            continue
        if marker:
            fence = marker.group(1)
            continue
        if line.startswith(("    ", "\t")):
            continue
        kept.append(line)
    return "\n".join(kept)


def review_section_names_fallback(body: str, head: str | None = None) -> bool:
    """Require one explicit completed-review line bound to the current head.

    Full-line matching excludes incidental prose, URLs and generated footers.
    Compare the entire captured SHA prefix so a stale longer SHA cannot pass
    merely because its first seven characters match.
    """
    if not head or len(head) < 7:
        return False
    body = _rendered_markdown(body or "")
    m = REVIEW_SECTION.search(body)
    if not m:
        return False
    rest = body[m.end() :]
    next_h = re.search(r"(?m)^##\s+", rest)
    section = rest[: next_h.start()] if next_h else rest
    # \n only: str.splitlines() also splits on U+2028 and friends.
    for line in section.split("\n"):
        if INCOMPLETE_REVIEW.search(line):
            continue
        attestation = FALLBACK_ATTESTATION.fullmatch(line.strip())
        if attestation and head.lower().startswith(attestation.group(2).lower()):
            return True
    return False


def p2_threads_closed(pr: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    for i, thread in enumerate(pr.get("reviewThreads", {}).get("nodes") or [], 1):
        comments = thread.get("comments", {}).get("nodes") or []
        if not comments:
            continue
        root = comments[0].get("body") or ""
        if not P2_ROOT.search(root):
            continue
        replies = comments[1:]
        if any(CLOSING.search(c.get("body") or "") for c in replies):
            continue
        failures.append(
            f"P2 thread #{i} has no closing reply (Notion link / fixed in <sha> / not-a-finding:)"
        )
    return failures


def evaluate(pr: dict[str, Any]) -> list[str]:
    reasons: list[str] = []
    body = pr.get("body") or ""
    head = pr.get("headRefOid") or ""
    # Rendered view: a heading inside a comment or fence is not visible.
    if not REVIEW_SECTION.search(_rendered_markdown(body)):
        reasons.append("PR body missing ## Review section")
    if not (codex_done_on_head(pr) or review_section_names_fallback(body, head)):
        reasons.append(
            "No completed Codex review on current head, and ## Review lacks a completed "
            "fallback attestation: Fallback review: <agy|antigravity|superpowers|claude-sonnet> "
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
