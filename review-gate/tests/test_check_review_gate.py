"""Run: python3 review-gate/tests/test_check_review_gate.py"""
import importlib.util
import inspect
import os
import re
from pathlib import Path

spec = importlib.util.spec_from_file_location(
    "check_review_gate",
    Path(__file__).parent.parent / "scripts" / "check-review-gate.py",
)
g = importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)

spec2 = importlib.util.spec_from_file_location(
    "merge_guard",
    Path(__file__).parent.parent / "scripts" / "merge-guard.py",
)
mg = importlib.util.module_from_spec(spec2)
spec2.loader.exec_module(mg)


def pr(**kwargs):
    base = {
        "body": "## Review\n\nCodex round 1\n",
        "author": {"login": "pr-author"},
        "baseRefName": "staging",
        "headRefOid": "abc1234",
        "labels": {"nodes": []},
        "reviews": {
            "nodes": [
                {
                    "state": "COMMENTED",
                    "body": "Codex findings",
                    "commit": {"oid": "abc1234"},
                    "author": {"login": "chatgpt-codex-connector"},
                }
            ]
        },
        "reviewThreads": {"nodes": []},
    }
    base.update(kwargs)
    return base


assert g.evaluate(pr()) == []

# Missing review section
bad = pr(body="No section here")
assert any("## Review" in r for r in g.evaluate(bad))

# Codex still Running on head
running = pr(
    reviews={
        "nodes": [
            {
                "state": "COMMENTED",
                "body": "Running",
                "commit": {"oid": "abc1234"},
                "author": {"login": "chatgpt-codex-connector"},
            }
        ]
    }
)
# body still names Codex in ## Review? Our ## Review says "Codex round 1" which
# is not a completed fallback attestation. So this should fail.
assert g.evaluate(running)

# Fallback review attestations must bind completion, reviewer and current head.
head = "89cda0610123456789abcdef0123456789abcdef"
pending_body = (
    "## Review\n\n"
    "Pending: adversarial review on head 89cda061 ...\n\n"
    "🤖 Generated with [Claude Code](https://claude.com/claude-code)\n"
)
assert g.evaluate(pr(body=pending_body, headRefOid=head, reviews={"nodes": []})), (
    "pending review plus Claude Code footer must never satisfy the gate"
)

for reviewer in ("codex", "agy", "antigravity", "superpowers", "claude-sonnet"):
    for sha in (head, head[:7], head[:8], head[:12]):
        for verdict in ("clean", "findings fixed"):
            body = (
                f"## Review\n\nFallback review: {reviewer} on {sha} "
                f"— verdict: {verdict}\n"
            )
            result = g.evaluate(pr(body=body, headRefOid=head, reviews={"nodes": []}))
            assert (result == []) == (sha == head), (sha, result)

# Clean Codex runs post no review, only a state marker in the summary PR comment.
def codex_comment(sha, status="completed", unresolved=False, login="chatgpt-codex-connector"):
    state = (
        '{"code_review":{"commit_sha":"%s","has_any_findings":%s,'
        '"has_unresolved_findings":%s,"status":"%s"}}'
        % (sha, str(unresolved).lower(), str(unresolved).lower(), status)
    )
    return {"author": {"login": login}, "body": f"<!-- codex-review-state:v1 {state} -->\nsummary"}

no_reviews = {"nodes": []}
assert g.evaluate(pr(headRefOid=head, reviews=no_reviews, comments={"nodes": [codex_comment(head)]})) == []
for bad in (
    codex_comment("deadbeef" + head[8:]),  # other head
    codex_comment(head, status="running"),
    codex_comment(head, unresolved=True),
    codex_comment(head, login="codex-helper"),
    {"author": {"login": "chatgpt-codex-connector"}, "body": "<!-- codex-review-state:v1 {not json} -->"},
):
    assert g.evaluate(pr(headRefOid=head, reviews=no_reviews, comments={"nodes": [bad]})), bad

invalid_lines = (
    "agy headless round 1\nhead: 89cda061",  # old independent keyword/SHA format
    "agy review completed on 89cda061",  # keyword-only, same line
    "Fallback review: agy on deadbee — verdict: clean",  # stale SHA
    "Fallback review: agy on 89cda061ffff — verdict: clean",  # shares 7 chars only
    "Fallback review: agy on 89cda0 — verdict: clean",  # too short
    f"Fallback review: agy on {head}0 — verdict: clean",  # too long
    "Fallback review: agy on 89cda061 — verdict: pending",
    "Fallback review: agy on 89cda061 — verdict: clean (pending)",
    "Pending: Fallback review: agy on 89cda061 — verdict: clean",
    "Fallback review: agy on 89cda061 — verdict: clean RUNNING",
    "TODO Fallback review: agy on 89cda061 — verdict: findings fixed",
    "Fallback review: agy on\n89cda061 — verdict: clean",  # split line
    "Fallback review: claude on 89cda061 — verdict: clean",  # ambiguous identity
    "Fallback review: someone on 89cda061 — verdict: clean",
    "Fallback review: agy on 89cda061 — verdict: unknown",
    "https://example.com/Fallback review: agy on 89cda061 — verdict: clean",
    "[Fallback review: agy on 89cda061 — verdict: clean](https://example.com)",
    # full head, so only the verdict or reviewer name can reject these
    f"Fallback review: agy on {head} — verdict: findings",
    f"Fallback review: none on {head} — verdict: clean",
    f"Fallback review: codex-bot on {head} — verdict: clean",
)
for line in invalid_lines:
    assert g.evaluate(
        pr(body=f"## Review\n\n{line}\n", headRefOid=head, reviews={"nodes": []})
    ), line

attestation = f"Fallback review: agy on {head} — verdict: clean"
# Strict PR-body grammar (Program 19:10, #105): no Markdown parsing, a physical-line allow-list.
R = "## Review"
ok_bodies = (
    f"{R}\n\n{attestation}\n",
    f"{R}\n{attestation}",
    f"Summary text.\n\n- a bullet\n\n{R}\n\nCodex high ran twice.\n\n{attestation}\n\n## Notes\n\n- `code` and [links](https://x) here\n",
    f"{R}\n\nRound 2 fixed in deadbeef.\n{attestation}\nfixed in deadbeef\nnot-a-finding: by design\n",
)
for body in ok_bodies:
    assert g.evaluate(pr(body=body, headRefOid=head, reviews={"nodes": []})) == [], body
# blank-surrounded exact attestation inside a fence or comment, the Program counterexample
for body in (f"{R}\n\n```text\n\n{attestation}\n\n```\n", f"{R}\n\n~~~\n\n{attestation}\n\n~~~\n",
             f"{R}\n\n<!--\n\n{attestation}\n\n-->\n", f"<!--\n\n{R}\n\n{attestation}\n\n-->\n",
             f"```\n\n{R}\n\n{attestation}\n\n```\n", f"{R}\n\n{attestation}\n\n   ```\n",
             f"x <!-- note -->\n\n{R}\n\n{attestation}\n"):
    reasons = g.evaluate(pr(body=body, headRefOid=head, reviews={"nodes": []}))
    assert any("fences" in r or "HTML comments" in r for r in reasons), body
# a line opening with `<` (after quote/list markers), anywhere in the body: raw HTML blocks survive blank
# lines, and an unterminated attribute (`<div title='`, Sonnet ef23aa3 P1) hides everything after it on GitHub
for opener in ("<pre>", "<PRE class=x>", "<script>", "<style>", "<textarea>", "<?x", "<!DOCTYPE x", "<![CDATA[", "- <pre>", "> <pre>",
               "<div title='", "<p title=\"", "<table x='", "<presentation> ok", "1. <div title='", "   <div title='", "<"):
    reasons = g.evaluate(pr(body=f"{opener}\n\n{R}\n\n{attestation}\n", headRefOid=head, reviews={"nodes": []}))
    assert any("starting with <" in r for r in reasons), opener
# `<` later in a line or escaped does not open a block (GitHub renderer, 2026-11-16): still allowed
for line in ("a <div title='", "- [ ] <div title='", "\\<div title='", "&lt;div title='", "Uses `<PR_NUMBER>` here"):
    assert g.evaluate(pr(body=f"{line}\n\n{R}\n\n{attestation}\n", headRefOid=head, reviews={"nodes": []})) == [], line
# the heading: exactly one exact line, after a blank line or at the top
for body in (f"{attestation}\n", f"{R}\n\n{attestation}\n\n{R}\n", f"## Review notes\n\n{attestation}\n",
             f"##\tReview\n\n{attestation}\n", f" {R}\n\n{attestation}\n", f"### Review\n\n{attestation}\n",
             f"[x]: /u '\n{R}\n{attestation}\n## x '\n"):
    assert g.evaluate(pr(body=body, headRefOid=head, reviews={"nodes": []})), body
# every non-blank region line: exact attestation, exact closing line, or plain prose
for line in (f"    {attestation}", f"\t{attestation}", f" {attestation}", f"- {attestation}", f"* {attestation}",
             f"1. {attestation}", f"1) {attestation}", f"> {attestation}", f"| {attestation} |", f"# {attestation}",
             f"### {attestation}", "===", "---", "***", "<div>", "<span>x</span>", "[x]: https://example.org", "[x](u)",
             "`code`", "text with `code`", "text (paren)", "text | pipe", "a > b", "| a | b |", "- note", "+ note",
             "2. note", "10) note", "<!-- -->", "\\- escaped", "&amp; entity first", "_emphasis_", "**bold**"):
    for body in (f"{R}\n\n{line}\n\n{attestation}\n", f"{R}\n\n{attestation}\n\n{line}\n", f"{R}\n{attestation}\n{line}\n"):
        reasons = g.evaluate(pr(body=body, headRefOid=head, reviews={"nodes": []}))
        assert reasons, body
        assert not g.review_section_names_fallback(body, head), body
# generic prose never authorises a non-exact attestation
for line in (f"{attestation} and more", f"Note {attestation}", f"{attestation} ", attestation.replace("—", "-"),
             f"{attestation}.", "Pending: " + attestation):
    assert not g.review_section_names_fallback(f"{R}\n\n{line}\n", head), line
# blank means only spaces and tabs (CommonMark): an NBSP/U+2028/form-feed/... line does not end an HTML
# block, so it neither precedes the heading nor counts as a blank region line
_UNI_BLANKS = ("\u00a0", "\u2028", "\u3000", "\x0c", "\x0b", "\x1c", "\x85", "\u200a")
for ws in _UNI_BLANKS:
    for opener in ("<details>", "<div>", "<a>", "<details><summary>"):
        body = f"{opener}\n{ws}\n{R}\n{attestation}\n"
        assert g.evaluate(pr(body=body, headRefOid=head, reviews={"nodes": []})), repr(body)
        assert not g.review_section_names_fallback(body, head), repr(body)
    assert g.evaluate(pr(body=f"{R}\n\n{ws}\n\n{attestation}\n", headRefOid=head, reviews={"nodes": []})), repr(ws)
for blank in (" ", "\t", " \t "):
    assert g.evaluate(pr(body=f"Intro\n{blank}\n{R}\n{blank}\n{attestation}\n", headRefOid=head, reviews={"nodes": []})) == []
# emphasis, strikethrough and math markers can span lines around the attestation
for line in ("x ~~y", "x *y", "x _y", "x $y", "z~~", "z*"):
    body = f"{R}\n{line}\n{attestation}\n"
    assert g.evaluate(pr(body=body, headRefOid=head, reviews={"nodes": []})), body
    assert not g.review_section_names_fallback(body, head), body
# each banned prose character, mid-line (Sonnet b on ea4fb8b, P1 4)
_NR = {"nodes": []}
for ch in "`<>|[]()*_~$":
    body = f"{R}\n\nnote {ch} here\n\n{attestation}\n"
    assert g.evaluate(pr(body=body, headRefOid=head, reviews=_NR)), body
    assert not g.review_section_names_fallback(body, head), body
for line in ("note: plain, words; 'quoted' - fine!", "1.5 seconds later", "1234567890. not a list marker"):
    assert g.evaluate(pr(body=f"{R}\n\n{line}\n\n{attestation}\n", headRefOid=head, reviews=_NR)) == [], line
for line in ("1.", "123456789. note", "1)"):
    assert g.evaluate(pr(body=f"{R}\n\n{line}\n\n{attestation}\n", headRefOid=head, reviews=_NR)), line
# CR and CRLF bodies read like LF ones, for passing and failing bodies alike
for nl in ("\r\n", "\r"):
    assert g.evaluate(pr(body=f"Intro{nl}{nl}{R}{nl}{nl}{attestation}{nl}", headRefOid=head, reviews=_NR)) == [], repr(nl)
    assert g.evaluate(pr(body=f"{R}{nl}{nl}```{nl}{nl}{attestation}{nl}", headRefOid=head, reviews=_NR)), repr(nl)
    assert g.evaluate(pr(body=f"Intro{nl}{R}{nl}{attestation}{nl}", headRefOid=head, reviews=_NR)), repr(nl)
# a tab-indented fence, raw-HTML openers behind tab/list/ordered prefixes, and trailing space on the heading
assert any("fences" in r for r in g.evaluate(pr(body=f"{R}\n\n\t```\n\n{attestation}\n", headRefOid=head, reviews=_NR)))
for opener in ("\t<pre>", "1. <pre>", "1) <script>", "* <style>", "+ <textarea>"):
    assert any("raw HTML" in r for r in g.evaluate(pr(body=f"{opener}\n\n{R}\n\n{attestation}\n", headRefOid=head, reviews=_NR))), opener
assert g.evaluate(pr(body=f"{R}  \n\n{attestation}\n", headRefOid=head, reviews=_NR)) == []
# the attestation names the full 40-hex head: any prefix (grindable) or a different head fails
assert g.review_section_names_fallback(f"{R}\n{attestation}", head[:7]) is False
for short in (head[:7], head[:12], head[:39]):
    assert not g.review_section_names_fallback(f"{R}\n\nFallback review: agy on {short} — verdict: clean\n", head), short
assert g.review_section_names_fallback(f"{R}\n\nFallback review: agy on {head.upper()} — verdict: clean\n", head)
assert g.review_section_names_fallback(f"{R}\n\n{attestation}\n", head)
# <details> anywhere: an unclosed one collapses the section that follows
for line in ("<details>", "<DETAILS open>", "text <details>", "<details><summary>x</summary>"):
    body = f"{line}\n\n{R}\n\n{attestation}\n"
    assert any("<details>" in r for r in g.evaluate(pr(body=body, headRefOid=head, reviews={"nodes": []}))), body
assert g.evaluate(pr(body=f"text <detailsx> ok\n\n{R}\n\n{attestation}\n", headRefOid=head, reviews={"nodes": []})) == []
# ASCII-only matching: re.I would otherwise fold U+017F to s
assert g.FALLBACK_ATTESTATION.fullmatch(f"Fallback review: claude-sonnet on {head} — verdict: clean")
assert not g.FALLBACK_ATTESTATION.fullmatch(f"Fallback review: claude-\u017fonnet on {head} — verdict: clean")
# the region ends at the next `## ` line: an attestation after it does not count
assert not g.review_section_names_fallback(f"{R}\n\nPending\n\n## Other\n\n{attestation}\n", head)
# the Claude Code footer belongs outside ## Review
assert g.evaluate(pr(body=f"{R}\n\n{attestation}\n\n🤖 Generated with [Claude Code](https://claude.com/claude-code)\n",
                     headRefOid=head, reviews={"nodes": []}))
assert g.evaluate(pr(body=f"{R}\n\n{attestation}\n\n## Footer\n\n🤖 Generated with [Claude Code](https://claude.com/claude-code)\n",
                     headRefOid=head, reviews={"nodes": []})) == []
# a well-formed region is required even when Codex reviewed the head on GitHub
assert g.evaluate(pr(body=f"{R}\n\n- bullet\n", headRefOid=head, reviews=no_reviews,
                     comments={"nodes": [codex_comment(head)]}))
# U+2028 stays inside one physical line
assert not g.review_section_names_fallback(f"{R}\n\nnote {attestation}\n", head)
assert g.evaluate(pr(body=f"{R}\n\n{attestation}\n", headRefOid="dddddddfffffffffff", reviews={"nodes": []}))
for missing_head in (None, "", "89cda0"):
    assert not g.review_section_names_fallback(f"{R}\n{attestation}", missing_head)

# merge guard: the same grammar decides `gh pr merge` (it calls gate.evaluate on the live payload)
_orig_parse, _orig_payload = mg.gate.parse_repo_with_host, mg.gate.pr_payload
mg.gate.parse_repo_with_host = lambda repo, cwd=None, env=None: (None, "owner", "target")
try:
    for body, allowed in ((f"{R}\n\n{attestation}\n", True),
                          (f"{R}\n\n```text\n\n{attestation}\n\n```\n", False),
                          (f"{R}\n\n<!--\n\n{attestation}\n\n-->\n", False),
                          (f"{R}\n\n- {attestation}\n", False),
                          (f"{R}\n\n> {attestation}\n", False),
                          (f"{R}\n\n    {attestation}\n", False),
                          (f"{R}\n\n| {attestation} |\n", False),
                          (f"{R}\n\n<pre>\n\n{attestation}\n", False),
                          (f"{R}\n\n[x]: https://example.org\n\n{attestation}\n", False),
                          (f"{R}\n\ntext\n===\n\n{attestation}\n", False),
                          (f"<details>\n\u00a0\n{R}\n{attestation}\n", False),
                          (f"{R}\nx ~~y\n{attestation}\nz~~\n", False),
                          (f"<details>\n\n{R}\n\n{attestation}\n", False)):
        mg.gate.pr_payload = lambda *a, _b=body, **k: pr(body=_b, headRefOid=head, reviews={"nodes": []})
        blocked = mg.check_one("gh -R owner/target pr merge 42 --squash", cwd="/tmp")
        assert (blocked is None) == allowed, (body, blocked)
    # one body per rule, each violating only that rule (Sonnet b on ea4fb8b, P1 5)
    single_rule = [f"{R}\n\nnote {ch} here\n\n{attestation}\n" for ch in "`<>|[]()*_~$"] + [
        f"{attestation}\n",  # no heading
        f"{R}\n\n{attestation}\n\n{R}\n",  # two headings
        f"Intro\n{R}\n\n{attestation}\n",  # heading not after a blank line
        f"{R}\n\n1. note\n\n{attestation}\n",  # ordered marker
        f"{R}\n\n~~~\n\n{attestation}\n",  # tilde fence
        f"{R}\n\n{attestation}\n\nx <!-- y\n",  # comment after the region
        f"<script>\n\n{R}\n\n{attestation}\n",  # raw HTML
        f"x <details>\n\n{R}\n\n{attestation}\n",  # details mid-line
        f"{R}\n\nFallback review: agy on 89cda06f — verdict: clean\n",  # stale SHA
    ]
    for body in single_rule:
        mg.gate.pr_payload = lambda *a, _b=body, **k: pr(body=_b, headRefOid=head, reviews={"nodes": []})
        assert mg.check_one("gh -R owner/target pr merge 42 --squash", cwd="/tmp"), body
    good = f"Intro\r\n\r\n{R}\r\n\r\n{attestation}\r\n"
    mg.gate.pr_payload = lambda *a, **k: pr(body=good, headRefOid=head, reviews={"nodes": []})
    assert mg.check_one("gh -R owner/target pr merge 42 --squash", cwd="/tmp") is None
    # a command the guard cannot resolve is blocked with its own reason, before any payload is read
    _err = mg.check_one("GH_CONFIG_DIR=~/e gh -R o/t pr merge 42", cwd="/tmp")
    assert _err and "dynamic GH_CONFIG_DIR" in _err, _err
    # Codex review on the head, the review:high label and P2 roots decide the merge too
    for kw, allowed in (({"reviews": {"nodes": [{"state": "COMMENTED", "body": "ok", "commit": {"oid": head},
                                                  "author": {"login": "chatgpt-codex-connector"}}]}}, True),
                        ({"reviews": {"nodes": []}}, False),
                        ({"baseRefName": "main", "labels": {"nodes": [{"name": "review:high"}]}}, True),
                        ({"baseRefName": "main"}, False),
                        ({"reviewThreads": {"nodes": [{"comments": {"nodes": [{"body": "_P2_ x"}]}}]}}, False)):
        payload = {"body": f"{R}\n\nCodex reviewed.\n", "headRefOid": head,
                   "reviews": {"nodes": [{"state": "COMMENTED", "body": "ok", "commit": {"oid": head},
                                          "author": {"login": "chatgpt-codex-connector"}}]}, **kw}
        mg.gate.pr_payload = lambda *a, _p=payload, **k: pr(**_p)
        blocked = mg.check_one("gh -R owner/target pr merge 42 --squash", cwd="/tmp")
        assert (blocked is None) == allowed, (kw, blocked)
    # P2 closure decides the merge too
    for reply, assoc, allowed in (("fixed in deadbeef", "MEMBER", True), ("fixed in deadbeef", "NONE", False),
                                  ("Thanks.\nfixed in deadbeef", "OWNER", False), ("fixed in deadbeef\n===", "OWNER", False),
                                  ("[Row](https://app.notion.com/p/abc)", "COLLABORATOR", True)):
        threads = {"nodes": [{"comments": {"nodes": [{"body": "P2: x"}, {"body": reply, "author": {"login": "reviewer"}, "authorAssociation": assoc}]}}]}
        mg.gate.pr_payload = lambda *a, _t=threads, **k: pr(body=f"{R}\n\n{attestation}\n", headRefOid=head,
                                                             reviews={"nodes": []}, reviewThreads=_t)
        blocked = mg.check_one("gh -R owner/target pr merge 42 --squash", cwd="/tmp")
        assert (blocked is None) == allowed, (reply, assoc, blocked)
finally:
    mg.gate.parse_repo_with_host, mg.gate.pr_payload = _orig_parse, _orig_payload

# check_one wiring: the real arguments reach parse_repo_with_host / pr_payload, under the merge child's gh env.
# `GH_REPO=` clears the selector (scrub), GH_HOST and a relative GH_CONFIG_DIR are overlaid against the tool cwd.
_calls = {}
def _rec_parse(repo, cwd=None, env=None):
    _calls["parse"] = (repo, cwd, dict(env) if env is not None else None, mg.gate._GH_SUBPROCESS_ENV.get())
    return ("ghe.example", "owner", "target")
def _rec_payload(owner, name, number, hostname=None):
    _calls["payload"] = (owner, name, number, hostname, mg.gate._GH_SUBPROCESS_ENV.get())
    return pr(body=f"{R}\n\n{attestation}\n", headRefOid=head, reviews={"nodes": []})
_old_env = os.environ.copy()
os.environ["GH_REPO"] = "evil/repo"
mg.gate.parse_repo_with_host, mg.gate.pr_payload = _rec_parse, _rec_payload
try:
    assert mg.check_one("GH_REPO= GH_HOST=ghe.example GH_CONFIG_DIR=cfg gh pr merge 42", cwd="/tmp/wire") is None, _calls
    _repo, _cwd, _env, _ctx = _calls["parse"]
    assert (_repo, _cwd) == (None, "/tmp/wire"), _calls["parse"][:2]
    assert _env is not None and "GH_REPO" not in _env, "scrubbed GH_REPO leaked into the gate env"
    assert _env["GH_HOST"] == "ghe.example" and _env["GH_CONFIG_DIR"] == "/tmp/wire/cfg", _env
    assert _ctx is not None and _ctx.get("GH_HOST") == "ghe.example" and "GH_REPO" not in _ctx, "gh_subprocess_env not active"
    _o, _n, _num, _host, _pctx = _calls["payload"]
    assert (_o, _n, _num, _host) == ("owner", "target", 42, "ghe.example"), _calls["payload"][:4]
    assert _pctx is _ctx or _pctx == _ctx, "pr_payload ran outside the child env"
    # any exception on the check path (not only RuntimeError) blocks with a message instead of escaping
    mg.gate.pr_payload = lambda *a, **k: (_ for _ in ()).throw(ValueError("bad json"))
    _msg = mg.check_one("gh -R owner/target pr merge 42", cwd="/tmp")
    assert _msg and _msg.startswith("review-gate: gate check failed: bad json"), _msg
finally:
    os.environ.clear(); os.environ.update(_old_env)
    mg.gate.parse_repo_with_host, mg.gate.pr_payload = _orig_parse, _orig_payload

# a P2 root never closes itself, even when its author may close and its first line is a closing token
_self_closing = {"body": "fixed in abc1234\n\nP2: x", "author": {"login": "owner"}, "authorAssociation": "OWNER"}
assert g.P2_ROOT.search(_self_closing["body"]) and g.closes(_self_closing["body"])
assert g.p2_threads_closed({"reviewThreads": {"nodes": [{"comments": {"nodes": [_self_closing]}}]}}), "root closed itself"
# no head OID: neither Codex path passes, even with a Codex review that carries no commit and a clean comment
_codex_nohead = {"state": "COMMENTED", "body": "ok", "commit": None, "author": {"login": "chatgpt-codex-connector"}}
for _h in ("", None):
    _p = {"headRefOid": _h, "reviews": {"nodes": [_codex_nohead]}, "comments": {"nodes": [codex_comment("")]}}
    assert g.codex_done_on_head(_p) is False and g.codex_clean_comment_on_head(_p) is False, _h

# Dismissed Codex review on head does not count
dismissed = pr(
    reviews={
        "nodes": [
            {
                "state": "DISMISSED",
                "body": "Codex findings",
                "commit": {"oid": "abc1234"},
                "author": {"login": "chatgpt-codex-connector"},
            }
        ]
    }
)
assert g.evaluate(dismissed)

# Human review that merely mentions "Codex" in the body does not count
human_mentions = pr(
    body="## Review\n\nwaiting\n",
    reviews={
        "nodes": [
            {
                "state": "COMMENTED",
                "body": "Codex did not run; please re-request.",
                "commit": {"oid": "abc1234"},
                "author": {"login": "mbernier"},
            }
        ]
    },
)
assert g.evaluate(human_mentions)
assert g.is_codex_author("chatgpt-codex-connector")
assert not g.is_codex_author("mbernier")
assert not g.is_codex_author("codex-helper")
assert not g.is_codex_author("chatgpt-user")

# Unanswered P2
p2 = pr(
    reviewThreads={
        "nodes": [
            {
                "comments": {
                    "nodes": [
                        {"body": "P2: add a test"},
                        {"body": "thanks"},
                    ]
                }
            }
        ]
    }
)
assert any("P2" in r for r in g.evaluate(p2))

def _p2(reply, assoc="MEMBER"):
    return pr(reviewThreads={"nodes": [{"comments": {"nodes": [{"body": "P2: add a test"},
                                                               {"body": reply, "author": {"login": "reviewer"}, "authorAssociation": assoc}]}}]})

# Closed P2
p2_ok = pr(
    reviewThreads={
        "nodes": [
            {
                "comments": {
                    "nodes": [
                        {"body": "P2: add a test"},
                        {"body": "fixed in `deadbeef`", "author": {"login": "reviewer"}, "authorAssociation": "MEMBER"},
                    ]
                }
            }
        ]
    }
)
assert g.evaluate(p2_ok) == []
# only an owner, member or collaborator closes: anyone can reply on a public repo
for assoc in ("OWNER", "MEMBER", "COLLABORATOR"):
    assert g.evaluate(_p2("fixed in deadbeef", assoc)) == [], assoc
for assoc in (None, "NONE", "CONTRIBUTOR", "FIRST_TIME_CONTRIBUTOR", "FIRST_TIMER", "MANNEQUIN", "member"):
    assert any("P2" in r for r in g.evaluate(_p2("fixed in deadbeef", assoc))), assoc


# A P2 reply closes only when its FIRST line starts, at column 0, with a closing token.
for ok in ("fixed in deadbeef", "fixed in `deadbeef`", "fixed in commit deadbeef1.", "fixed in deadbeef  ",
           "not-a-finding: intentional, see SKILL.md", "Tracked: https://app.notion.com/p/4194efecc95a816c",
           "https://www.notion.so/abc123", "[Tracker row](https://app.notion.com/p/abc)",
           "fixed in deadbeef\n\n```\nanything after the first line\n```", "fixed in deadbeef\n \t\nmore",
           "fixed in deadbeef\r\n\r\nmore", "fixed in deadbeef\n"):
    assert g.evaluate(_p2(ok)) == [], ok
    assert g.closes(ok), ok
for bad in ("Thanks.\nfixed in deadbeef", " fixed in deadbeef", "\tfixed in deadbeef", "- fixed in deadbeef",
            "1. fixed in deadbeef", "> fixed in deadbeef", "```\nfixed in deadbeef\n```", "<!-- fixed in deadbeef -->",
            "`fixed in deadbeef`", "Still open; eventually reply with `fixed in deadbeef`", "will be not-a-finding: maybe",
            "fixed in deadbeefzz", "not-fixed:https://notion.so/ticket", "`https://notion.so/ticket`",
            "https://evilnotion.so/ticket", "\nfixed in deadbeef", "    fixed in deadbeef",
            # the next line would make the first a setext heading or a table header
            "fixed in 0123456\n===", "not-a-finding: x\n---", "not-a-finding: a|b\n-|-\nc|d", "fixed in 0123456\r===",
            "fixed in 0123456\nmore text", "fixed in 0123456\n\u00a0\nmore",
            # link text must be visible
            "[](https://notion.so/x)", "[\u200b](https://notion.so/x)", "[![](https://notion.so/x)",
            "[ ](https://notion.so/x)", "[a<!--](https://notion.so/x)-->", "[a>b](https://notion.so/x)",
            "not-a-finding: <!-- -->", "not-a-finding: &nbsp;", "not-a-finding: \u200b", "not-a-finding: \u2800",
            "not-a-finding: _", "fixed in \u017f0123456",
            # nothing may follow the SHA or the link on the first line
            "fixed in 0000000 — not actually fixed, ignore", "fixed in commit deadbeef1 — details", "fixed in `deadbeef",
            "fixed in deadbeef`", "[x](https://notion.so/a", "[x](https://notion.so/a) not tracked", "<https://notion.so/x",
            "https://notion.so/x is not where this is tracked"):
    assert any("P2" in r for r in g.evaluate(_p2(bad))), bad
for ok in ("<https://notion.so/x>", "Tracked: <https://www.notion.so/x>", "tracked https://notion.com/x",
           "FIXED IN DEADBEEF", "fixed in 0123456", "fixed in commit `0123456789abcdef0123456789abcdef01234567`"):
    assert g.closes(ok), ok
for bad in ("https://notion.so.evil.com/x", "https://notion.sox/x", "fixed in 012345", "not-a-finding:",
            "not-a-finding:   ", "fixed in 0123456\r\nmore"):
    assert not g.closes(bad), bad
# the root is P2 by word, any case; any one closing reply closes; the root cannot close itself
for root in ("P2: x", "p2 x", "nit (P2)"):
    t = pr(reviewThreads={"nodes": [{"comments": {"nodes": [{"body": root, "author": {"login": "reviewer"}, "authorAssociation": "OWNER"}]}}]})
    assert any("P2" in r for r in g.evaluate(t)), root
t = pr(reviewThreads={"nodes": [{"comments": {"nodes": [{"body": "P2: fixed in deadbeef", "author": {"login": "reviewer"}, "authorAssociation": "OWNER"}]}}]})
assert any("P2" in r for r in g.evaluate(t))
for root in ("xp2 note", "P20 note", "mp2y"):
    t = pr(reviewThreads={"nodes": [{"comments": {"nodes": [{"body": root}]}}]})
    assert g.evaluate(t) == [], root
t = pr(reviewThreads={"nodes": [{"comments": {"nodes": [{"body": "P2: x"}, {"body": "thanks", "author": {"login": "reviewer"}, "authorAssociation": "OWNER"},
                                                        {"body": "fixed in deadbeef", "author": {"login": "reviewer"}, "authorAssociation": "MEMBER"}]}}]})
assert g.evaluate(t) == []
for root in ("_P2_ x", "P2_x", "see p2."):
    t = pr(reviewThreads={"nodes": [{"comments": {"nodes": [{"body": root}]}}]})
    assert any("P2" in r for r in g.evaluate(t)), root
assert not g.closes("https://notion.so/ is not where this is tracked")
# Codex completion: only a completed, non-pending review or clean marker by the exact bot on the exact head
_cx = lambda **kw: {"state": "COMMENTED", "body": "findings", "commit": {"oid": head},
                    "author": {"login": "chatgpt-codex-connector"}, **kw}
assert g.codex_done_on_head(pr(headRefOid=head, reviews={"nodes": [_cx()]}))
for rev in (_cx(state="PENDING"), _cx(state="pending"), _cx(state="DISMISSED"), _cx(body="Running review"),
            _cx(body="Running " + "x" * 391), _cx(commit={"oid": head[:12]}), _cx(commit=None),
            _cx(author={"login": "chatgpt-codex-connectorx"}), _cx(author={"login": "xchatgpt-codex-connector"})):
    assert not g.codex_done_on_head(pr(headRefOid=head, reviews={"nodes": [rev]})), rev
assert g.codex_done_on_head(pr(headRefOid=head, reviews={"nodes": [_cx(body="Running " + "x" * 392)]}))
assert g.codex_done_on_head(pr(headRefOid=head, reviews={"nodes": [_cx(author={"login": "ChatGPT-Codex-Connector"})]}))
def _marker(**kw):
    review = {"commit_sha": head, "status": "completed", "has_unresolved_findings": False, **kw}
    return {"author": {"login": "chatgpt-codex-connector"},
            "body": "<!-- codex-review-state:v1 " + __import__("json").dumps({"code_review": review}) + " -->"}
assert g.codex_clean_comment_on_head(pr(headRefOid=head, comments={"nodes": [_marker()]}))
for c in (_marker(status="queued"), _marker(status="Completed"), _marker(has_unresolved_findings=None),
          _marker(has_unresolved_findings=0), _marker(commit_sha=head[:12]), _marker(commit_sha=head.upper())):
    assert not g.codex_clean_comment_on_head(pr(headRefOid=head, comments={"nodes": [c]})), c
for login in ("chatgpt-codex-connectorx", "chatgpt-codex-connector[bot]", "chatgpt-codex", ""):
    assert not g.is_codex_author(login), login
# a non-matching first marker must not hide a valid later one in the same comment
_two = codex_comment("deadbeef" + head[8:])
_two["body"] += "\n" + codex_comment(head)["body"]
assert g.evaluate(pr(headRefOid=head, reviews=no_reviews, comments={"nodes": [_two]})) == []

# main without label
main = pr(baseRefName="main")
assert any("review:high" in r for r in g.evaluate(main))
main_ok = pr(baseRefName="main", labels={"nodes": [{"name": "review:high"}]})
assert g.evaluate(main_ok) == []
# review:ultra is retired: it no longer satisfies the main label requirement
assert any("review:high" in r for r in g.evaluate(pr(baseRefName="main", labels={"nodes": [{"name": "review:ultra"}]})))

# merge guard parsing — including spaced -R / trailing -R / --repo forms
assert mg.extract_pr_and_repo("gh pr merge 42 --squash") == (42, None)
assert mg.extract_pr_and_repo("gh -R bernierllc/email_demo pr merge 99 --auto") == (
    99,
    "bernierllc/email_demo",
)
assert mg.extract_pr_and_repo("gh pr merge 99 -R owner/repo --squash") == (99, "owner/repo")
assert mg.extract_pr_and_repo("gh --repo=owner/repo pr merge 5") == (5, "owner/repo")
assert mg.extract_pr_and_repo("gh --repo owner/repo pr merge 5") == (5, "owner/repo")
assert mg.MERGE_RE.search("gh pr merge 1 --squash")
assert mg.is_gh_pr_merge("gh pr merge 1 --squash")
assert mg.is_gh_pr_merge("gh pr -R owner/target merge 42")
assert not mg.is_gh_pr_merge("gh pr view 1")
# ``merge`` as --body data is not the pr subcommand
assert not mg.is_gh_pr_merge("gh pr comment 42 --body merge")
assert mg._direct_gh_pr_non_merge("gh pr comment 42 --body merge")
assert mg.check_command("gh pr comment 42 --body merge", cwd="/tmp") is None
assert not mg.MERGE_RE.search("gh pr view 1")
assert mg.OVERRIDE.search("gh pr merge 1  # review-gate-ok: matt said so")
assert mg.has_override("gh pr merge 1  # review-gate-ok: matt said so")
assert mg.extract_repo("gh pr -R owner/target merge 42") == "owner/target"
assert mg.extract_repo("GH_REPO=owner/target gh pr merge 42") == "owner/target"
assert mg.extract_merge_selector("gh pr -R owner/target merge 42") == "42"
# Quoted body text must not count as the Bash escape comment
assert not mg.has_override(
    "gh pr merge 42 --body 'notes # review-gate-ok: placeholder'"
)
assert not mg.has_override(
    'gh pr merge 42 --body "notes # review-gate-ok: placeholder"'
)
# Heredoc / prior-line markers are not attached to the merge segment
assert not mg.has_override(
    "cat <<'EOF'\n# review-gate-ok: fake\nEOF\ngh pr merge 42"
)
assert not mg.has_override("# review-gate-ok: prior line\ngh pr merge 42")
assert mg.has_override("gh pr merge 42  # review-gate-ok: attached")
# Nested process-substitution / backtick comments are not outer-shell overrides
assert not mg.segment_has_override(
    "gh -R owner/target pr merge 42 --auto 3< <(printf x # review-gate-ok: fake\n)"
)
assert not mg.segment_has_override(
    "gh -R owner/target pr merge 42 --body `printf x # review-gate-ok: fake\n`"
)
# Escaped whitespace before # is not a shell comment (body text, not override)
assert not mg.segment_has_override(
    r"gh -R owner/target pr merge 42 --body=\ #review-gate-ok:\ fake"
)
assert not mg._is_unescaped_shell_comment_hash(r"\ #review-gate-ok: fake", 2)
# GIT_DIR / GIT_CONFIG_* without -R fails closed; with -R is allowed
assert mg.sets_git_location("GIT_DIR=/workspace/target/.git gh pr merge 42")
assert mg.sets_git_location(
    "GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=url.https://ghe.example/o/t.git.insteadOf "
    "GIT_CONFIG_VALUE_0=https://github.com/o/s.git gh pr merge 42"
)
git_dir_err = mg.check_command(
    "GIT_DIR=/workspace/target/.git gh pr merge 42", cwd="/tmp"
)
assert git_dir_err and "GIT_DIR" in git_dir_err
git_cfg_err = mg.check_command(
    "GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=foo GIT_CONFIG_VALUE_0=bar gh pr merge 42",
    cwd="/tmp",
)
assert git_cfg_err and "GIT_CONFIG" in git_cfg_err
segs, err = mg.iter_merge_segments(
    "GIT_DIR=/workspace/target/.git gh -R owner/r pr merge 42", "/tmp"
)
assert err is None and len(segs) == 1
# GH_CONFIG_DIR / XDG_CONFIG_HOME / HOME are propagated to gate gh subprocesses
child = mg._child_gh_env(
    "GH_CONFIG_DIR=/tmp/enterprise gh -R owner/target pr merge 42",
    scrub_gh_repo=False,
)
assert child is not None and child.get("GH_CONFIG_DIR") == "/tmp/enterprise"
child = mg._child_gh_env(
    "XDG_CONFIG_HOME=/tmp/enterprise gh -R owner/target pr merge 42",
    scrub_gh_repo=False,
)
assert child is not None and child.get("XDG_CONFIG_HOME") == "/tmp/enterprise"
child = mg._child_gh_env(
    "HOME=/tmp/enterprise-home gh -R owner/target pr merge 42",
    scrub_gh_repo=False,
)
assert child is not None and child.get("HOME") == "/tmp/enterprise-home"
# Cleared config vars are popped so the gate does not keep the hook's Enterprise dir
_prev_config = os.environ.get("GH_CONFIG_DIR")
_prev_xdg = os.environ.get("XDG_CONFIG_HOME")
_prev_host = os.environ.get("GH_HOST")
os.environ["GH_CONFIG_DIR"] = "/tmp/hook-enterprise"
os.environ["XDG_CONFIG_HOME"] = "/tmp/hook-xdg"
os.environ["GH_HOST"] = "ghe.hook"
try:
    cleared = mg._child_gh_env(
        "env -u GH_CONFIG_DIR gh -R owner/target pr merge 42",
        scrub_gh_repo=False,
    )
    assert cleared is not None and "GH_CONFIG_DIR" not in cleared
    cleared_i = mg._child_gh_env(
        "env -i gh -R owner/target pr merge 42",
        scrub_gh_repo=False,
    )
    assert cleared_i is not None
    assert "GH_CONFIG_DIR" not in cleared_i
    assert "XDG_CONFIG_HOME" not in cleared_i
    assert "HOME" not in cleared_i
    assert "GH_HOST" not in cleared_i
finally:
    if _prev_config is None:
        os.environ.pop("GH_CONFIG_DIR", None)
    else:
        os.environ["GH_CONFIG_DIR"] = _prev_config
    if _prev_xdg is None:
        os.environ.pop("XDG_CONFIG_HOME", None)
    else:
        os.environ["XDG_CONFIG_HOME"] = _prev_xdg
    if _prev_host is None:
        os.environ.pop("GH_HOST", None)
    else:
        os.environ["GH_HOST"] = _prev_host
# Override on one merge must not waive a second merge in the same command
assert mg.segment_has_override("gh -R owner/safe pr merge 1  # review-gate-ok: approved")
assert not mg.segment_has_override("gh -R owner/target pr merge 2")
_called_ovr = {"n": 0}
_orig_one_ovr = mg.check_one


def _count_ovr(segment, cwd=None):
    _called_ovr["n"] += 1
    return f"blocked:{segment}"


mg.check_one = _count_ovr
try:
    ovr_compound = mg.check_command(
        "gh -R owner/safe pr merge 1  # review-gate-ok: approved\n"
        "gh -R owner/target pr merge 2",
        cwd="/tmp",
    )
    assert ovr_compound and "blocked:" in ovr_compound and _called_ovr["n"] == 1
finally:
    mg.check_one = _orig_one_ovr
# Query/fragment suffixes on pull URLs still count (and beat conflicting -R)
assert mg.is_pull_url_selector("https://github.com/owner/target/pull/7?foo=bar")
assert mg.is_pull_url_selector("https://github.com/owner/target/pull/7#discussion")
n, r, e, scrub = mg.resolve_pr_number(
    "gh pr merge 'https://github.com/owner/target/pull/7?foo=bar' -R owner/safe"
)
assert e is None and n == 7 and r == "github.com/owner/target" and scrub is False
# Codex review with missing commit.oid must not satisfy the current head
assert not g.codex_done_on_head(
    pr(
        reviews={
            "nodes": [
                {
                    "state": "COMMENTED",
                    "body": "Codex findings",
                    "commit": None,
                    "author": {"login": "chatgpt-codex-connector"},
                }
            ]
        }
    )
)
assert not g.codex_done_on_head(
    pr(
        reviews={
            "nodes": [
                {
                    "state": "COMMENTED",
                    "body": "Codex findings",
                    "commit": {},
                    "author": {"login": "chatgpt-codex-connector"},
                }
            ]
        }
    )
)
# Compound commands require literal -R (cwd/cd/export chains are not modeled)
segs, err = mg.iter_merge_segments(
    "cd /workspace/other && gh pr merge 42 --squash", "/tmp/start"
)
assert segs == [] and err and "compound" in err
segs, err = mg.iter_merge_segments(
    "cd /workspace/other && gh -R owner/r pr merge 42 --squash", "/tmp/start"
)
assert err is None and segs == [("gh -R owner/r pr merge 42 --squash", "/tmp/start")]
segs, err = mg.iter_merge_segments(
    "cd /workspace/other\ngh -R owner/r pr merge 42 --squash", "/tmp/start"
)
assert err is None and len(segs) == 1
segs, err = mg.iter_merge_segments(
    "pushd /workspace/other && gh -R owner/r pr merge 42 --squash", "/tmp/start"
)
assert err is None and len(segs) == 1
segs, err = mg.iter_merge_segments(
    "gh -R owner/a pr merge 1 --match-head-commit deadbeef || gh -R owner/b pr merge 2",
    "/tmp/start",
)
assert err is None and [s for s, _ in segs] == [
    "gh -R owner/a pr merge 1 --match-head-commit deadbeef",
    "gh -R owner/b pr merge 2",
]
segs, err = mg.iter_merge_segments('cd "$OTHER_REPO" && gh pr merge 42', "/tmp/start")
assert segs == [] and err and "compound" in err
assert mg.extract_merge_selector("gh pr merge --squash") is None
assert (
    mg.extract_merge_selector("gh pr merge --match-head-commit deadbeef --auto") is None
)
assert mg.extract_merge_selector("gh pr merge -b 'message' --auto") is None
assert mg.extract_merge_selector(
    "gh pr merge https://github.com/o/r/pull/7 --squash"
) == "https://github.com/o/r/pull/7"
assert mg.extract_merge_selector("gh pr merge feature-branch --squash") == "feature-branch"
# Branch selectors must be placed after ``pr view`` (not ``gh pr <branch> view``)
_captured_view: list[list[str]] = []
_real_run = mg.subprocess.run


def _capture_view_run(args, **kwargs):  # type: ignore[no-untyped-def]
    _captured_view.append(list(args))
    class _Proc:
        returncode = 0
        stdout = '{"number":9,"url":"https://github.com/owner/target/pull/9"}'
        stderr = ""

    return _Proc()


mg.subprocess.run = _capture_view_run
try:
    n, r, e, scrub = mg.resolve_pr_number(
        "gh -R owner/target pr merge feature-branch --squash"
    )
    assert e is None and n == 9 and r == "owner/target"
    assert _captured_view and _captured_view[0][:4] == [
        "gh",
        "pr",
        "view",
        "feature-branch",
    ]
    assert "--json" in _captured_view[0]
    _captured_view.clear()
    n, r, e, scrub = mg.resolve_pr_number(
        "gh -R owner/target pr merge -- -release"
    )
    assert e is None and n == 9
    assert _captured_view and _captured_view[0][:5] == [
        "gh",
        "pr",
        "view",
        "--",
        "-release",
    ]
finally:
    mg.subprocess.run = _real_run
# URL selector must carry host/owner/repo (dotcom kept explicit for --hostname)
n, r, e, scrub = mg.resolve_pr_number(
    "gh pr merge https://github.com/owner/other/pull/7 --squash"
)
assert e is None and n == 7 and r == "github.com/owner/other" and scrub is False
# URL selector wins over a conflicting -R (matches gh)
n, r, e, scrub = mg.resolve_pr_number(
    "gh pr merge https://github.com/owner/target/pull/7 -R owner/safe --squash"
)
assert e is None and n == 7 and r == "github.com/owner/target" and scrub is False
# Scheme-less path-shaped selectors are branch names, not pull URLs
n, r, e, scrub = mg.resolve_pr_number(
    "gh -R owner/target pr merge feature/owner/safe/pull/7"
)
assert not (e is None and n == 7 and r and "owner/safe" in (r or ""))
assert mg.is_pull_url_selector("feature/owner/safe/pull/7") is None
assert mg.is_pull_url_selector("github.com/owner/safe/pull/7") is None
assert mg.is_pull_url_selector("https://github.com/owner/safe/pull/7") is not None
# Enterprise pull URLs retain the hostname for gate queries
n, r, e, scrub = mg.resolve_pr_number(
    "gh pr merge https://ghe.example/owner/repo/pull/7 --squash"
)
assert e is None and n == 7 and r == "ghe.example/owner/repo" and scrub is False
# Command-scoped GH_HOST overlays process env for fallback gh resolution
child = mg._child_gh_env("GH_HOST=ghe.example gh pr merge 42", scrub_gh_repo=False)
assert child is not None and child.get("GH_HOST") == "ghe.example"
# Only direct `gh` (optional leading `env`) is allowed — reject ssh/xargs/…
assert mg.gh_is_direct_command("gh -R owner/target pr merge 42")
assert mg.gh_is_direct_command("env GH_HOST=ghe.example gh -R owner/t pr merge 42")
assert not mg.gh_is_direct_command("ssh buildbox gh pr merge 42")
assert not mg.gh_is_direct_command("xargs gh -R owner/target pr merge")
# Dynamic / ANSI-C / pathname-expanded executable names must not bypass the gate
dyn = r"$'\x67\x68' -R owner/target pr merge 42"
assert not mg.is_gh_pr_merge(dyn)
assert mg.dynamic_gh_pr_merge(dyn)
blocked = mg.check_command(dyn, cwd="/tmp")
assert blocked and "dynamic" in blocked
assert mg.dynamic_gh_pr_merge("$(printf gh) -R owner/target pr merge 42")
assert mg.dynamic_gh_pr_merge("./[g]h -R owner/target pr merge 42")
assert mg.dynamic_gh_pr_merge("gh? -R owner/target pr merge 42")
blocked = mg.check_command("./[g]h -R owner/target pr merge 42", cwd="/tmp")
assert blocked and "dynamic" in blocked
# Dynamic merge in a later segment must not be ignored after a literal merge
compound_dyn = (
    r"gh -R owner/safe pr merge 1; $'\x67\x68' -R owner/target pr merge 2"
)
blocked = mg.check_command(compound_dyn, cwd="/tmp")
assert blocked and "dynamic" in blocked
assert not mg.dynamic_gh_pr_merge("something pr merge 42")
assert not mg.dynamic_gh_pr_merge("gh -R owner/target pr merge 42")
# Option terminator: post-`--` `-R…` is a branch selector, not a repo flag
assert (
    mg.extract_repo("gh -R owner/current pr merge -- -Rowner/branch")
    == "owner/current"
)
assert (
    mg.extract_merge_selector("gh -R owner/current pr merge -- -Rowner/branch")
    == "-Rowner/branch"
)
# Doc heredoc bodies to cat are not executable merge segments
heredoc_cmd = "cat > example.sh <<'EOF'\ngh -R owner/repo pr merge 42\nEOF"
assert mg.check_command(heredoc_cmd, cwd="/tmp") is None
assert not mg.executable_heredoc_merge(heredoc_cmd)
assert not any(
    mg.is_gh_pr_merge(p) for p, _ in mg.split_shell_chains(heredoc_cmd)
)
# bash << executes the body — fail closed
bash_heredoc = "bash <<'EOF'\ngh -R owner/target pr merge 2\nEOF"
assert mg.executable_heredoc_merge(bash_heredoc)
bash_hd_err = mg.check_command(bash_heredoc, cwd="/tmp")
assert bash_hd_err and "heredoc" in bash_hd_err
# Unquoted heredoc expands $(gh … pr merge) even for cat
unquoted_hd = "cat <<EOF\n$(gh -R owner/target pr merge 2)\nEOF"
assert mg.executable_heredoc_merge(unquoted_hd)
# Array-assembled merge: a=(g\h … pr merge); "${a[@]}"
array_merge = 'a=(g\\h -R owner/target pr merge 2); "${a[@]}"'
assert mg.array_assembled_merge(array_merge)
array_err = mg.check_command(array_merge, cwd="/tmp")
assert array_err and "array" in array_err
assert mg.array_assembled_merge("cmds=(gh -R owner/safe pr merge 1)")
assert not mg.array_assembled_merge('echo "${PATH[@]}"')
# Positional-parameter assembly across segments
positional_merge = 'set -- gh -R owner/target pr; set -- "$@" merge 2; "$@"'
assert mg.positional_assembled_merge(positional_merge)
pos_err = mg.check_command(positional_merge, cwd="/tmp")
assert pos_err and (
    "positional" in pos_err or "$@" in pos_err or "array" in pos_err
)
assert mg.positional_assembled_merge('set -- gh -R owner/target pr merge 2; "$@"')
assert not mg.positional_assembled_merge('echo "$@"')
assert not mg.positional_assembled_merge("gh -R owner/safe pr merge 1")
# gh alias set / opaque gh <alias> can expand to pr merge
alias_cmd = (
    'p=pr; m=merge; gh alias set sneak "$p $m 2 -R owner/target"; gh sneak'
)
assert mg.gh_alias_merge_risk(alias_cmd)
alias_err = mg.check_command(alias_cmd, cwd="/tmp")
assert alias_err and "alias" in alias_err
assert mg.gh_alias_merge_risk("gh sneak")
assert mg.gh_alias_merge_risk("gh alias set sneak 'pr merge 2'")
assert not mg.gh_alias_merge_risk("gh alias list")
assert not mg.gh_alias_merge_risk("gh -R owner/safe pr merge 1")
# Multiword alias / flags before alias name
assert mg.gh_alias_merge_risk("gh pr sneak")
assert mg.gh_alias_merge_risk("gh -R owner/target sneak")
assert mg.gh_alias_merge_risk(
    "gh alias set 'pr sneak' 'pr merge 2 -R owner/target'; gh pr sneak"
)
# Multiword aliases under every namespace (not only pr)
assert mg.gh_alias_merge_risk("gh repo sneak")
assert mg.gh_alias_merge_risk(
    "gh alias set 'repo sneak' 'pr merge 2 -R owner/target'; gh repo sneak"
)
assert mg.gh_alias_merge_risk("gh issue sneak")
assert mg.gh_alias_merge_risk("gh run sneak")
# Nested third-level aliases under known second-level namespaces
assert mg.gh_alias_merge_risk("gh repo autolink sneak")
assert mg.gh_alias_merge_risk(
    "gh alias set 'repo autolink sneak' 'pr merge 2 -R owner/target'; "
    "gh repo autolink sneak"
)
assert mg.gh_alias_merge_risk("gh repo deploy-key sneak")
assert mg.gh_alias_merge_risk("gh codespace ports sneak")
assert mg.gh_alias_merge_risk("gh issue artifact sneak")
assert not mg.gh_alias_merge_risk("gh repo autolink list")
assert not mg.gh_alias_merge_risk("gh repo deploy-key list")
assert not mg.gh_alias_merge_risk("gh codespace ports forward")
# Built-ins must not be treated as opaque aliases
assert not mg.gh_alias_merge_risk("gh discussion list")
assert not mg.gh_alias_merge_risk("gh skill list")
assert not mg.gh_alias_merge_risk("gh repo view")
assert not mg.gh_alias_merge_risk("gh copilot")
assert not mg.gh_alias_merge_risk("gh preview")
assert not mg.gh_alias_merge_risk("gh agent-task list")
assert not mg.gh_alias_merge_risk("gh licenses")
# Same-line command after heredoc opener must still be gated
same_line = "cat <<EOF; gh -R owner/repo pr merge 42\nbody\nEOF"
assert any(mg.is_gh_pr_merge(p) for p, _ in mg.split_shell_chains(same_line))
# Here-strings are not heredocs
assert "<<<" in mg.strip_heredoc_bodies("cat <<<'gh pr merge 42'")
# Escaped / mixed-quoted heredoc openers quote-remove to the real delimiter
escaped = "cat <<E\\OF\nbody\nEOF\ngh -R owner/repo pr merge 42"
assert any(mg.is_gh_pr_merge(p) for p, _ in mg.split_shell_chains(escaped))
assert "gh -R owner/repo pr merge 42" in mg.strip_heredoc_bodies(escaped)
mixed = 'cat <<"E"OF\nbody\nEOF\ngh -R owner/repo pr merge 42'
assert any(mg.is_gh_pr_merge(p) for p, _ in mg.split_shell_chains(mixed))
# Relative config after prior pushd (compound) — fail closed
pushd_rel = "(pushd /tmp/enterprise; GH_CONFIG_DIR=.gh gh -R owner/target pr merge 42)"
assert mg.gh_config_relative_after_chdir(pushd_rel)
blocked = mg.check_command(pushd_rel, cwd="/tmp")
assert blocked and "relative" in blocked
# Dynamic pr/merge subcommands after literal gh
assert mg.dynamic_gh_subcommand_merge('gh "$x" "$y" 42 -R owner/target')
assert mg.dynamic_gh_subcommand_merge('gh pr "$y" 42 -R owner/target')
assert mg.dynamic_gh_subcommand_merge('gh "$x" merge 42 -R owner/target')
# Unquoted $x may word-split into `pr merge`
assert mg.dynamic_gh_subcommand_merge("gh $x 42 -R owner/target")
assert mg.check_command("gh $x 42 -R owner/target", cwd="/tmp")
assert not mg.dynamic_gh_subcommand_merge("gh pr merge 42 -R owner/target")
assert not mg.dynamic_gh_subcommand_merge('gh issue "$x"')
# Fully variable-assembled merge across segments (no literal gh/pr/merge on invoke)
var_asm = 'c=gh; p=pr; m=merge; "$c" "$p" "$m" 42 -R owner/repo'
assert mg.variable_assembled_merge(var_asm)
var_asm_err = mg.check_command(var_asm, cwd="/tmp")
assert var_asm_err and "variable-assembled" in var_asm_err
assert mg.variable_assembled_merge(
    'c=gh p=pr m=merge "$c" "$p" "$m" 42 -R owner/repo'
)
assert not mg.variable_assembled_merge('"$c" "$p" "$m" 42 -R owner/repo')
assert not mg.variable_assembled_merge("gh -R owner/safe pr merge 1")
# printf -v assigns merge words the same as NAME=value
printf_asm = (
    'printf -v c gh; printf -v p pr; printf -v m merge; '
    '"$c" "$p" "$m" 42 -R owner/repo'
)
assert mg.variable_assembled_merge(printf_asm)
assert mg._part_assigns_merge_assembly_words("printf -v c gh") == {"gh"}
assert mg._part_assigns_merge_assembly_words("printf -vc pr") == {"pr"}
assert mg._part_assigns_merge_assembly_words("printf -v m %s merge") == {"merge"}
printf_asm_err = mg.check_command(printf_asm, cwd="/tmp")
assert printf_asm_err and "variable-assembled" in printf_asm_err
# read here-string / array form also assigns merge words
read_asm = 'c=gh; p=pr; read m <<< merge; "$c" "$p" "$m" 42 -R owner/repo'
assert mg.variable_assembled_merge(read_asm)
assert mg._part_assigns_merge_assembly_words("read m <<< merge") == {"merge"}
assert mg._part_assigns_merge_assembly_words("read m <<<merge") == {"merge"}
assert mg._part_assigns_merge_assembly_words(
    'read -a a <<< "gh pr merge"'
) == {"gh", "pr", "merge"}
assert mg._part_assigns_merge_assembly_words(
    "read m <<EOF\nmerge\nEOF"
) == {"merge"}
read_asm_err = mg.check_command(read_asm, cwd="/tmp")
assert read_asm_err and "variable-assembled" in read_asm_err
# Append-stitched merge words (c=g; c+=h → gh)
append_asm = (
    'c=g; c+=h; p=pr; m=mer; m+=ge; "$c" "$p" "$m" 42 -R owner/repo'
)
assert mg.variable_assembled_merge(append_asm)
append_asm_err = mg.check_command(append_asm, cwd="/tmp")
assert append_asm_err and "variable-assembled" in append_asm_err
assert mg.variable_assembled_merge(
    'c=g c+=h p=pr m=mer m+=ge "$c" "$p" "$m" 42 -R owner/repo'
)
# Substring / other transforms can yield gh/pr/merge without exact source words
xform_asm = (
    'c=xgh; p=xpr; m=xmerge; "${c:1}" "${p:1}" "${m:1}" 42 -R owner/repo'
)
assert mg.variable_assembled_merge(xform_asm)
xform_asm_err = mg.check_command(xform_asm, cwd="/tmp")
assert xform_asm_err and "variable-assembled" in xform_asm_err
assert mg.variable_assembled_merge(
    'c=xgh; p=pr; m=merge; "${c#x}" "$p" "$m" 42 -R owner/repo'
)
assert mg._param_expansion_transformed("${c:1}")
assert not mg._param_expansion_transformed("$c")
assert not mg._param_expansion_transformed("${c}")
# printf -v formatting can assemble merge words (e.g. '%sh' g → gh)
fmt_asm = (
    "printf -v c '%sh' g; p=pr; m=merge; "
    '"$c" "$p" "$m" 42 -R owner/repo'
)
assert mg.variable_assembled_merge(fmt_asm)
assert mg._part_assigns_merge_assembly_words("printf -v c '%sh' g") == {"gh"}
assert mg._part_assigns_merge_assembly_words("printf -v c %s%s g h") == {"gh"}
fmt_asm_err = mg.check_command(fmt_asm, cwd="/tmp")
assert fmt_asm_err and "variable-assembled" in fmt_asm_err
# Dynamic argv after merge may expand into -Rowner/target
dyn_repo_flag = 'gh pr merge 42 "$(printf -- -Rowner/target)"'
assert mg.dynamic_merge_argv(dyn_repo_flag)
dyn_repo_err = mg.check_command(dyn_repo_flag, cwd="/tmp")
assert dyn_repo_err and "dynamic argv" in dyn_repo_err
assert not mg.dynamic_merge_argv("gh -R owner/target pr merge 42 --auto")
# Brace expansion can inject extra -R flags after the inspected ones
brace_cmd = "gh -R owner/safe pr merge 1 {-Rowner/safe,-Rowner/target}"
assert mg.dynamic_merge_argv(brace_cmd)
brace_err = mg.check_command(brace_cmd, cwd="/tmp")
assert brace_err and ("dynamic" in brace_err or "argv" in brace_err)
assert mg.redefines_gh(
    "alias -- gh='/usr/bin/gh -R owner/target pr merge 2'; "
    "gh -R owner/safe pr merge 1"
)
alias_opt_err = mg.check_command(
    "shopt -s expand_aliases; "
    "alias -- gh='/usr/bin/gh -R owner/target pr merge 2'; "
    "gh -R owner/safe pr merge 1",
    cwd="/tmp",
)
assert alias_opt_err and ("alias" in alias_opt_err or "function" in alias_opt_err)
blocked = mg.check_command(
    'x=pr; y=merge; gh "$x" "$y" 42 -R owner/target', cwd="/tmp"
)
assert blocked and "subcommand" in blocked
# env -S can construct gh inside the split-string operand
assert mg.env_split_string_merge_risk("env -S 'g''h -R owner/target' pr merge 42")
assert mg.env_split_string_merge_risk("env -S 'gh -R owner/target pr merge 42'")
blocked = mg.check_command("env -S 'g''h -R owner/target' pr merge 42", cwd="/tmp")
# quote-smash may trip first; either fail-closed path is OK
assert blocked and ("split-string" in blocked or "quote" in blocked)
assert mg.env_split_string_merge_risk("env -S 'g''h -R owner/target' pr merge 42")
# Relative config dir under env -C resolves against different cwds — fail closed
assert mg.gh_config_relative_after_chdir(
    "env -C /tmp/enterprise GH_CONFIG_DIR=.gh gh -R owner/target pr merge 42"
)
_n, _repo, _err, _scrub = mg.resolve_pr_number(
    "env -C /tmp/enterprise GH_CONFIG_DIR=.gh gh -R owner/target pr merge 42"
)
assert _n is None and _err and "relative" in _err
assert not mg.gh_config_relative_after_chdir(
    "GH_CONFIG_DIR=.gh gh -R owner/target pr merge 42"
)
# Relative config without chdir is allowed but resolved against the tool cwd
rel_child = mg._child_gh_env(
    "GH_CONFIG_DIR=.gh gh -R owner/target pr merge 42",
    scrub_gh_repo=False,
    cwd="/tmp/enterprise",
)
assert rel_child is not None
assert rel_child.get("GH_CONFIG_DIR") == "/tmp/enterprise/.gh"
assert not mg.gh_config_relative_after_chdir(
    "env -C /tmp/enterprise GH_CONFIG_DIR=/tmp/enterprise/.gh gh -R owner/target pr merge 42"
)
xargs_err = mg.check_command(
    "printf '42\\n' | xargs gh -R owner/target pr merge", cwd="/tmp"
)
assert xargs_err and "directly executed" in xargs_err
ssh_err = mg.check_command("ssh buildbox gh pr merge 42", cwd="/tmp")
assert ssh_err and "directly executed" in ssh_err
segs, err = mg.iter_merge_segments("ssh buildbox gh -R owner/target pr merge 42", "/tmp")
assert segs == [] and err and "directly executed" in err
# Leading GH_HOST= prefixes a hostless -R / GH_REPO slug
assert (
    mg.extract_repo("GH_HOST=ghe.example gh -R owner/target pr merge 42")
    == "ghe.example/owner/target"
)
assert (
    mg.extract_repo("GH_HOST=ghe.example GH_REPO=owner/target gh pr merge 42")
    == "ghe.example/owner/target"
)
# Already-hosted -R keeps its host; github.com GH_HOST stays explicit
assert (
    mg.extract_repo("GH_HOST=ghe.example gh -R other.ghe/owner/target pr merge 42")
    == "other.ghe/owner/target"
)
assert mg.extract_repo("GH_HOST=github.com gh -R owner/target pr merge 42") == (
    "github.com/owner/target"
)
assert mg.extract_repo('GH_HOST="$HOST" gh -R owner/target pr merge 42') == (
    "$UNRESOLVED"
)
# ``env GH_HOST=…`` wrappers also prefix hostless -R (matches gh help environment)
assert (
    mg.extract_repo("env GH_HOST=ghe.example gh -R owner/target pr merge 42")
    == "ghe.example/owner/target"
)
assert (
    mg.extract_repo("env -C /tmp GH_HOST=ghe.example gh -R owner/target pr merge 42")
    == "ghe.example/owner/target"
)
assert (
    mg.extract_repo(
        "env --chdir=/tmp GH_HOST=ghe.example GH_REPO=owner/target gh pr merge 42"
    )
    == "ghe.example/owner/target"
)
assert mg.extract_repo('env GH_HOST="$HOST" gh -R owner/target pr merge 42') == (
    "$UNRESOLVED"
)
# ``env -u GH_HOST`` / ``-i`` / sticky / bare ``-`` force explicit github.com
assert (
    mg.extract_repo("env -u GH_HOST gh -R owner/target pr merge 42")
    == "github.com/owner/target"
)
assert (
    mg.extract_repo("env --unset GH_HOST gh -R owner/target pr merge 42")
    == "github.com/owner/target"
)
assert (
    mg.extract_repo("env -uGH_HOST gh -R owner/target pr merge 42")
    == "github.com/owner/target"
)
assert (
    mg.extract_repo("env -i gh -R owner/target pr merge 42")
    == "github.com/owner/target"
)
assert (
    mg.extract_repo("env - gh -R owner/target pr merge 42")
    == "github.com/owner/target"
)
assert (
    mg.extract_repo("env -u GH_HOST GH_HOST=ghe.other gh -R owner/target pr merge 42")
    == "ghe.other/owner/target"
)
# Empty ``GH_HOST=`` is an explicit reset to github.com (not "absent")
assert (
    mg.extract_repo("GH_HOST= gh -R owner/target pr merge 42")
    == "github.com/owner/target"
)
assert (
    mg.extract_repo("env GH_HOST= gh -R owner/target pr merge 42")
    == "github.com/owner/target"
)
# Empty / cleared GH_REPO resets to the tool cwd (scrub process GH_REPO)
repo, scrub = mg.extract_repo_resolution("GH_REPO= gh pr merge 42")
assert repo is None and scrub is True
repo, scrub = mg.extract_repo_resolution("env -u GH_REPO gh pr merge 42")
assert repo is None and scrub is True
repo, scrub = mg.extract_repo_resolution("env -uGH_REPO gh pr merge 42")
assert repo is None and scrub is True
repo, scrub = mg.extract_repo_resolution("gh -R owner/target pr merge 42")
assert repo == "owner/target" and scrub is False
assert g.parse_repo_with_host(r) == ("ghe.example", "owner", "repo")
assert g.parse_repo("github.com/owner/repo") == ("owner", "repo")
assert g.parse_repo("owner/repo") == ("owner", "repo")
assert g.parse_repo_with_host("owner/repo") == (None, "owner", "repo")
assert g.parse_repo_with_host("github.com/owner/repo") == (
    "github.com",
    "owner",
    "repo",
)
assert g.parse_repo_with_host("ghe.example/owner/repo") == (
    "ghe.example",
    "owner",
    "repo",
)
assert mg.extract_repo("gh pr merge 7 -Rowner/other --squash") == "owner/other"
assert mg.extract_repo("gh -Rowner/other pr merge 7") == "owner/other"
# Last repeated -R/--repo wins (matches gh)
assert mg.extract_repo("gh pr merge 7 -R owner/safe -R owner/target") == "owner/target"
assert mg.extract_repo("gh pr merge 7 --repo=owner/safe --repo=owner/target") == (
    "owner/target"
)
# -R inside --body text must not count as the repository flag
assert mg.extract_repo("gh pr merge 7 --body 'note -R owner/safe'") is None
segs, err = mg.iter_merge_segments(
    "gh -R owner/safe pr merge 1 | gh -R owner/target pr merge 2", "/tmp"
)
assert err is None and len(segs) == 2
assert segs[0][0] == "gh -R owner/safe pr merge 1"
assert segs[1][0] == "gh -R owner/target pr merge 2"
scoped = mg.check_command("env -C /workspace/other gh pr merge 42", cwd="/tmp")
assert scoped and "command-scoped" in scoped
# All GNU env chdir spellings require -R
for env_cmd in (
    "env --chdir=/workspace/other gh pr merge 42",
    "env --chdir /workspace/other gh pr merge 42",
    "env -C/workspace/other gh pr merge 42",
):
    err = mg.check_command(env_cmd, cwd="/tmp")
    assert err and "command-scoped" in err, env_cmd
# Compound without -R fails closed (including quoted separators / comments / export)
for compound_cmd in (
    "echo 'ignored; cd /workspace/safe' && gh pr merge 42",
    "cd /definitely-missing || gh pr merge 42",
    "cd /workspace/safe & gh pr merge 42",
    "(cd /workspace/other && gh pr merge 42)",
    "echo \\\ncd /workspace/safe && gh pr merge 42",
    "source /tmp/move-to-other-repo.sh && gh pr merge 42",
    ". /tmp/move-to-other-repo.sh && gh pr merge 42",
    "echo ok # ignored && cd /workspace/safe\ngh pr merge 42",
    "export GH_REPO=owner/target && gh pr merge 42",
    "false && cd /workspace/safe; gh pr merge 42",
    "(echo setup; cd /workspace/safe); gh pr merge 42",
    "if cd /workspace/other; then gh pr merge 42; fi",
):
    segs, err = mg.iter_merge_segments(compound_cmd, "/tmp/start")
    assert segs == [] and err and "compound" in err, compound_cmd
# Same compounds with literal -R are allowed
for ok_cmd in (
    "cd /definitely-missing || gh -R owner/r pr merge 42",
    "(cd /workspace/other && gh -R owner/r pr merge 42)",
    "export GH_REPO=owner/target && gh -R owner/r pr merge 42",
    "false && cd /workspace/safe; gh -R owner/r pr merge 42",
    "(echo setup; cd /workspace/safe); gh -R owner/r pr merge 42",
    "if cd /workspace/other; then gh -R owner/r pr merge 42; fi",
):
    segs, err = mg.iter_merge_segments(ok_cmd, "/tmp/start")
    assert err is None and len(segs) == 1 and mg.has_literal_repo(segs[0][0]), ok_cmd
# source/. before merge is rejected by check_command even with literal -R
source_ok_segs, source_ok_err = mg.iter_merge_segments(
    "source /tmp/move-to-other-repo.sh && gh -R owner/r pr merge 42", "/tmp/start"
)
assert source_ok_err is None and len(source_ok_segs) == 1
# Same-segment GH_REPO= still counts as literal repo
assert mg.extract_repo("GH_REPO=owner/target gh pr merge 99") == "owner/target"
assert mg.has_literal_repo("GH_REPO=owner/target gh pr merge 99")
# Shell wrappers must not bypass the gate
wrapped = mg.check_command("bash -c 'gh pr merge 42'", cwd="/tmp")
assert wrapped and "shell-wrapped" in wrapped
wrapped = mg.check_command("eval 'gh pr merge 42'", cwd="/tmp")
assert wrapped and "shell-wrapped" in wrapped
# Quote-concatenation hides `gh` from MERGE_RE / shlex inside wrappers
smash = "bash -c 'g''h -R owner/target pr merge 42'"
assert mg.quote_smashed_merge(smash)
smash_err = mg.check_command(smash, cwd="/tmp")
assert smash_err and ("quote" in smash_err or "concatenat" in smash_err)
assert not mg.quote_smashed_merge("bash -c 'gh -R owner/target pr merge 42'")
# Wrapped merge in one segment must not be masked by a literal merge in another
subshell_merge = (
    "echo $(gh -R owner/target pr merge 2 --auto); "
    "gh -R owner/safe pr merge 1 --auto"
)
wrapped = mg.check_command(subshell_merge, cwd="/tmp")
assert wrapped and "shell-wrapped" in wrapped
# Nested $(merge) in the SAME segment as a direct merge
nested_same = (
    'X="$(gh -R owner/target pr merge 2 --auto)" '
    "gh -R owner/safe pr merge 1 --auto"
)
assert mg.nested_merge_in_segment(nested_same)
nested_err = mg.check_command(nested_same, cwd="/tmp")
assert nested_err and ("nested" in nested_err or "shell-wrapped" in nested_err)
# Nameref can mutate GH_HOST without naming it in an assignment
nameref_cmd = (
    "declare -n host=GH_HOST; host=ghe.example; "
    "gh -R owner/target pr merge 42"
)
assert mg.nameref_with_merge(nameref_cmd)
nameref_err = mg.check_command(nameref_cmd, cwd="/tmp")
assert nameref_err and (
    "nameref" in nameref_err.lower() or "declare -n" in nameref_err
)
# Prior export of GH_HOST/config is not mirrored into the merge-segment gate env
export_host = "export GH_HOST=ghe.example; gh -R owner/target pr merge 42"
assert mg.prior_tracked_gh_export(export_host)
export_err = mg.check_command(export_host, cwd="/tmp")
assert export_err and "exported" in export_err
declare_host = "declare -x GH_HOST=ghe.example; gh -R owner/target pr merge 42"
assert mg.prior_tracked_gh_export(declare_host)
assert mg.check_command(declare_host, cwd="/tmp") and "exported" in mg.check_command(
    declare_host, cwd="/tmp"
)
assert mg.prior_tracked_gh_export(
    "typeset -x GH_HOST=ghe.example; gh -R owner/target pr merge 42"
)
# declare without -x still keeps an inherited export attribute
declare_plain = "declare GH_HOST=ghe.example; gh -R owner/target pr merge 42"
assert mg._part_exports_tracked_gh("declare GH_HOST=ghe.example")
assert mg.prior_tracked_gh_export(declare_plain)
assert mg.check_command(declare_plain, cwd="/tmp") and "exported" in mg.check_command(
    declare_plain, cwd="/tmp"
)
# readonly NAME=value also assigns before locking (keeps inherited export)
readonly_host = "readonly GH_HOST=ghe.example; gh -R owner/target pr merge 42"
assert mg._part_exports_tracked_gh("readonly GH_HOST=ghe.example")
assert mg.prior_tracked_gh_export(readonly_host)
assert mg.check_command(readonly_host, cwd="/tmp") and "exported" in mg.check_command(
    readonly_host, cwd="/tmp"
)
# for/select loop targets assign NAME while keeping inherited export
assert mg._part_exports_tracked_gh("for GH_HOST in ghe.example")
for_host = "for GH_HOST in ghe.example; do :; done; gh -R owner/safe pr merge 1"
assert mg.prior_tracked_gh_export(for_host)
for_err = mg.check_command(for_host, cwd="/tmp")
assert for_err and "exported" in for_err
assert mg._part_exports_tracked_gh("select GH_CONFIG_DIR in /tmp/a")
assert mg.prior_tracked_gh_export(
    "select GH_CONFIG_DIR in /tmp/a; do break; done; "
    "gh -R owner/target pr merge 42"
)
# Same-segment leading assign is still OK (mirrored by _child_gh_env)
assert not mg.prior_tracked_gh_export(
    "GH_HOST=ghe.example gh -R owner/target pr merge 42"
)
# Standalone assignment keeps export attribute for the merge child only
assert mg._part_exports_tracked_gh("GH_HOST=ghe.example")
standalone_assign = "GH_HOST=ghe.example; gh -R owner/target pr merge 42"
assert mg.prior_tracked_gh_export(standalone_assign)
assert mg.check_command(standalone_assign, cwd="/tmp") and "exported" in mg.check_command(
    standalone_assign, cwd="/tmp"
)
# Indirect writers (printf -v / read / mapfile) also mutate inherited exports
printf_host = "printf -v GH_HOST ghe.example; gh -R owner/target pr merge 42"
assert mg._part_exports_tracked_gh("printf -v GH_HOST ghe.example")
assert mg.prior_tracked_gh_export(printf_host)
printf_err = mg.check_command(printf_host, cwd="/tmp")
assert printf_err and "exported" in printf_err
assert mg._part_exports_tracked_gh("printf -vGH_HOST ghe.example")
assert mg._part_exports_tracked_gh("read GH_HOST")
assert mg.prior_tracked_gh_export(
    "mapfile GH_CONFIG_DIR; gh -R owner/target pr merge 42"
)
# Prior unset of tracked GH_* is not mirrored into the gate env
unset_host = "unset GH_HOST; gh -R owner/target pr merge 42"
assert mg.prior_tracked_gh_unset(unset_host)
unset_err = mg.check_command(unset_host, cwd="/tmp")
assert unset_err and "unset" in unset_err
# Indexed unset spelling removes the scalar the same as unset GH_HOST
assert mg._part_unsets_tracked_gh("unset 'GH_HOST[0]'")
assert mg.prior_tracked_gh_unset(
    "unset 'GH_HOST[0]'; gh -R owner/target pr merge 42"
)
assert mg.check_command(
    "unset 'GH_HOST[0]'; gh -R owner/target pr merge 42", cwd="/tmp"
)
# Dynamic unset target may expand to GH_HOST at runtime
assert mg._part_unsets_tracked_gh('unset "$v"')
dyn_unset = 'v=GH_HOST; unset "$v"; gh -R owner/safe pr merge 1'
assert mg.prior_tracked_gh_unset(dyn_unset)
dyn_unset_err = mg.check_command(dyn_unset, cwd="/tmp")
assert dyn_unset_err and "unset" in dyn_unset_err
assert mg._part_unsets_tracked_gh('export -n "$v"')
assert mg.prior_tracked_gh_unset(
    'export -n "$v"; gh -R owner/safe pr merge 1'
)
assert mg._part_unsets_tracked_gh('declare +x "$v"')
assert mg.prior_tracked_gh_unset(
    'declare +x "$v"; gh -R owner/safe pr merge 1'
)
# declare +x / export -n remove export attribute (same class as unset)
declare_plusx = "declare +x GH_HOST; gh -R owner/target pr merge 42"
assert mg._part_unsets_tracked_gh("declare +x GH_HOST")
assert mg.prior_tracked_gh_unset(declare_plusx)
assert mg.check_command(declare_plusx, cwd="/tmp")
assert mg._part_unsets_tracked_gh("export -n GH_HOST")
assert mg.prior_tracked_gh_unset("export -n GH_HOST; gh -R owner/target pr merge 42")
# Inherited relative GH_CONFIG_DIR + chdir → fail closed
_prev_gh_cfg = os.environ.get("GH_CONFIG_DIR")
os.environ["GH_CONFIG_DIR"] = ".gh"
try:
    inherited_cd = "cd /tmp/enterprise; gh -R owner/target pr merge 42"
    assert mg._inherited_relative_gh_config()
    assert mg.gh_config_relative_after_chdir(inherited_cd)
    inherited_err = mg.check_command(inherited_cd, cwd="/tmp")
    assert inherited_err and "relative" in inherited_err
finally:
    if _prev_gh_cfg is None:
        os.environ.pop("GH_CONFIG_DIR", None)
    else:
        os.environ["GH_CONFIG_DIR"] = _prev_gh_cfg

# Inherited PATH with `.` + cd can run /tmp/fake/gh after chdir
assert mg._path_has_relative_component(".:/usr/bin")
assert mg._path_has_relative_component("/usr/bin:bin")
assert not mg._path_has_relative_component("/usr/bin:/bin")
_prev_path = os.environ.get("PATH")
os.environ["PATH"] = ".:/usr/bin"
try:
    rel_path_cd = "cd /tmp/fake; gh -R owner/safe pr merge 1"
    assert mg._inherited_relative_path()
    assert mg.relative_path_after_chdir(rel_path_cd)
    rel_path_err = mg.check_command(rel_path_cd, cwd="/tmp")
    assert rel_path_err and "PATH" in rel_path_err
    assert not mg.relative_path_after_chdir(
        "gh -R owner/safe pr merge 1"
    )  # no chdir
finally:
    if _prev_path is None:
        os.environ.pop("PATH", None)
    else:
        os.environ["PATH"] = _prev_path

# Function/alias/hash named gh shadows the binary under inspection
gh_func = (
    'm=merge; gh(){ /usr/bin/gh -R owner/target pr "$m" 2; }; '
    "gh -R owner/safe pr merge 1"
)
assert mg.redefines_gh(gh_func)
redef_err = mg.check_command(gh_func, cwd="/tmp")
assert redef_err and ("function" in redef_err or "alias" in redef_err)
assert mg.redefines_gh("alias gh=/tmp/fake-gh; gh -R owner/safe pr merge 1")
assert not mg.redefines_gh("gh -R owner/safe pr merge 1")
# BASH_CMDS[gh]=… inserts into the command hash table (like hash -p)
assert mg._part_bash_cmds_override("BASH_CMDS[gh]=/tmp/fake")
bash_cmds = "BASH_CMDS[gh]=/tmp/fake; gh -R owner/safe pr merge 1"
assert mg.redefines_gh(bash_cmds)
bash_cmds_err = mg.check_command(bash_cmds, cwd="/tmp")
assert bash_cmds_err and (
    "function" in bash_cmds_err or "alias" in bash_cmds_err or "hash" in bash_cmds_err
)
assert mg.redefines_gh('BASH_CMDS["$x"]=/tmp/fake; gh -R owner/safe pr merge 1')
assert mg.redefines_gh(
    "case x in x) BASH_CMDS[gh]=/tmp/fake;; esac; gh -R owner/safe pr merge 1"
)
# gh() defined behind if/while/until still shadows later merges
if_redef = "if gh(){ /tmp/evil; }; then :; fi; gh -R owner/safe pr merge 1"
assert mg.redefines_gh(if_redef)
assert mg.GH_FUNC_RE.search("if gh(){ /tmp/evil; }")
if_redef_err = mg.check_command(if_redef, cwd="/tmp")
assert if_redef_err and ("function" in if_redef_err or "alias" in if_redef_err)
assert mg.redefines_gh(
    "while gh(){ /tmp/evil; }; do break; done; gh -R owner/safe pr merge 1"
)
assert mg.redefines_gh(
    "until alias gh=/tmp/fake; do break; done; gh -R owner/safe pr merge 1"
)
# gh()/alias/hash defined inside a brace group still shadows later merges
brace_redef = "{ gh(){ /tmp/evil; }; }; gh -R owner/safe pr merge 1"
assert mg.redefines_gh(brace_redef)
assert mg.GH_FUNC_RE.search("{ gh(){ /tmp/evil; }; }")
brace_redef_err = mg.check_command(brace_redef, cwd="/tmp")
assert brace_redef_err and (
    "function" in brace_redef_err or "alias" in brace_redef_err
)
assert mg.redefines_gh(
    "{ alias gh=/tmp/fake; }; gh -R owner/safe pr merge 1"
)
assert mg.redefines_gh(
    "{ hash -p /tmp/fake gh; }; gh -R owner/safe pr merge 1"
)
assert mg.redefines_prefix_builtin(
    "{ command(){ /tmp/evil; }; }; gh -R owner/safe pr merge 1"
)
# gh()/alias/hash defined inside a case arm still shadows later merges
case_redef = "case x in x) gh(){ /tmp/evil; };; esac; gh -R owner/safe pr merge 1"
assert mg.redefines_gh(case_redef)
assert mg.GH_FUNC_RE.search("case x in x) gh(){ /tmp/evil; }")
case_redef_err = mg.check_command(case_redef, cwd="/tmp")
assert case_redef_err and (
    "function" in case_redef_err or "alias" in case_redef_err
)
assert mg.redefines_gh(
    "case x in x) alias gh=/tmp/fake;; esac; gh -R owner/safe pr merge 1"
)
assert mg.redefines_gh(
    "case x in x) hash -p /tmp/fake gh;; esac; gh -R owner/safe pr merge 1"
)
# ``builtin hash`` / ``command hash`` remember a pathname for gh
builtin_hash = "builtin hash -p /tmp/fake gh; gh -R owner/safe pr merge 1"
assert mg.redefines_gh(builtin_hash)
builtin_hash_err = mg.check_command(builtin_hash, cwd="/tmp")
assert builtin_hash_err and (
    "hash" in builtin_hash_err or "function" in builtin_hash_err or "alias" in builtin_hash_err
)
assert mg.redefines_gh("command hash -p /tmp/fake gh; gh -R owner/safe pr merge 1")
assert mg.redefines_gh("hash -p /tmp/fake gh; gh -R owner/safe pr merge 1")
# Dynamic hash name: hash -p /tmp/fake "$x" with x=gh
dyn_hash = 'x=gh; hash -p /tmp/fake "$x"; gh -R owner/safe pr merge 1'
assert mg._part_hash_override_risk('hash -p /tmp/fake "$x"')
assert mg.redefines_gh(dyn_hash)
dyn_hash_err = mg.check_command(dyn_hash, cwd="/tmp")
assert dyn_hash_err and (
    "hash" in dyn_hash_err or "alias" in dyn_hash_err or "function" in dyn_hash_err
)
# Brace-expanded hash name: g{h,h} → gh gh
brace_hash = "hash -p /tmp/fake g{h,h}; gh -R owner/safe pr merge 1"
assert mg._var_target_dynamic("g{h,h}")
assert mg._part_hash_override_risk("hash -p /tmp/fake g{h,h}")
assert mg.redefines_gh(brace_hash)
brace_hash_err = mg.check_command(brace_hash, cwd="/tmp")
assert brace_hash_err and (
    "hash" in brace_hash_err or "alias" in brace_hash_err or "function" in brace_hash_err
)
# ``builtin alias`` / ``command alias`` define the same shell alias
builtin_alias = (
    "shopt -s expand_aliases; "
    "m=merge; "
    "builtin alias gh='/usr/bin/gh -R owner/target pr \"$m\" 2; # '; "
    "gh -R owner/safe pr merge 1"
)
assert mg.redefines_gh(builtin_alias)
builtin_alias_err = mg.check_command(builtin_alias, cwd="/tmp")
assert builtin_alias_err and (
    "alias" in builtin_alias_err or "function" in builtin_alias_err
)
assert mg.redefines_gh(
    "command alias gh=/tmp/fake-gh; gh -R owner/safe pr merge 1"
)
assert mg.redefines_prefix_builtin(
    "builtin alias command=true; command gh -R owner/safe pr merge 1"
)
# Repeated builtin/command prefixes still define the alias
nested_builtin_alias = (
    "shopt -s expand_aliases; "
    "builtin builtin alias gh='/tmp/fake'; "
    "gh -R owner/safe pr merge 1"
)
assert mg.redefines_gh(nested_builtin_alias)
assert mg.GH_ALIAS_RE.search("builtin builtin alias gh=/tmp/fake")
nested_err = mg.check_command(nested_builtin_alias, cwd="/tmp")
assert nested_err and (
    "alias" in nested_err or "function" in nested_err
)
assert mg.redefines_gh(
    "command builtin alias gh=/tmp/fake; gh -R owner/safe pr merge 1"
)
assert mg.redefines_gh(
    "builtin builtin hash -p /tmp/fake gh; gh -R owner/safe pr merge 1"
)
# Quote-concatenated alias name: g'h' → gh after Bash quote-removal
quote_alias = (
    "shopt -s expand_aliases\n"
    "m=merge\n"
    "alias g'h'='/usr/bin/gh -R owner/target pr \"$m\" 2; # '\n"
    "gh -R owner/safe pr merge 1"
)
assert mg.redefines_gh(quote_alias)
quote_alias_err = mg.check_command(quote_alias, cwd="/tmp")
assert quote_alias_err and ("alias" in quote_alias_err or "function" in quote_alias_err)
assert mg.redefines_gh(
    "alias g\"h\"=/tmp/fake-gh; gh -R owner/safe pr merge 1"
)
assert mg.redefines_prefix_builtin(
    "alias c'ommand'=true; command gh -R owner/safe pr merge 1"
)
# Backslash quote-removal: g\h → gh
bs_alias = (
    "shopt -s expand_aliases; "
    "m=merge; "
    r"alias g\h='/usr/bin/gh -R owner/target pr \"$m\" 2; # '; "
    "gh -R owner/safe pr merge 1"
)
assert mg.redefines_gh(bs_alias)
bs_err = mg.check_command(bs_alias, cwd="/tmp")
assert bs_err and ("alias" in bs_err or "function" in bs_err)
# Dynamically assembled gh inside bash -c
dyn_wrap = "bash -c 'x=g; x+=h; \"$x\" -R owner/target pr merge 2'"
assert mg.opaque_shell_wrapper_pr_merge(dyn_wrap)
dyn_wrap_err = mg.check_command(dyn_wrap, cwd="/tmp")
assert dyn_wrap_err and (
    "shell-wrapped" in dyn_wrap_err or "dynamic" in dyn_wrap_err
)
assert mg.opaque_shell_wrapper_pr_merge(
    "eval 'x=g; x+=h; \"$x\" -R owner/target pr merge 2'"
)
assert not mg.opaque_shell_wrapper_pr_merge("bash -c 'echo hello'")
assert not mg.opaque_shell_wrapper_pr_merge("bash -c 'echo pr merge'")
# Inherited export -f gh (BASH_FUNC_gh%%) shadows the inspected binary
assert mg.inherited_shadowing_function(
    "gh -R owner/safe pr merge 1",
    env={"BASH_FUNC_gh%%": "() { /usr/bin/gh -R owner/target pr merge 2; }"},
)
assert mg.inherited_shadowing_function(
    "command gh -R owner/safe pr merge 1",
    env={"BASH_FUNC_command%%": "() { true; }"},
)
assert not mg.inherited_shadowing_function(
    "gh -R owner/safe pr merge 1", env={}
)
_bash_func_key = "BASH_FUNC_gh%%"
_prev_bash_func = os.environ.get(_bash_func_key)
os.environ[_bash_func_key] = "() { /usr/bin/gh -R owner/target pr merge 2; }"
try:
    inh_err = mg.check_command("gh -R owner/safe pr merge 1", cwd="/tmp")
    assert inh_err and "BASH_FUNC" in inh_err
finally:
    if _prev_bash_func is None:
        os.environ.pop(_bash_func_key, None)
    else:
        os.environ[_bash_func_key] = _prev_bash_func
# Local command_not_found_handle + unresolved gx … pr merge bypasses MERGE_RE
local_cnf = (
    "command_not_found_handle(){ /tmp/evil; }; gx -R owner/safe pr merge 1"
)
assert mg.defines_command_not_found_handle(local_cnf)
local_cnf_err = mg.check_command(local_cnf, cwd="/tmp")
assert local_cnf_err and "command_not_found" in local_cnf_err
assert mg.defines_command_not_found_handle(
    "function command_not_found_handle { /tmp/evil; }; "
    "gx -R owner/safe pr merge 1"
)
assert not mg.defines_command_not_found_handle(
    "command_not_found_handle(){ true; }; echo hi"
)
# Inherited command_not_found_handle can run a merge for unresolved gx … pr merge
assert mg.inherited_shadowing_function(
    "gx -R owner/safe pr merge 1",
    env={
        "BASH_FUNC_command_not_found_handle%%": (
            "() { /usr/bin/gh -R owner/target pr merge 2; }"
        )
    },
)
assert not mg.inherited_shadowing_function(
    "gx -R owner/safe pr merge 1", env={}
)
_cnf_key = "BASH_FUNC_command_not_found_handle%%"
_prev_cnf = os.environ.get(_cnf_key)
os.environ[_cnf_key] = "() { /usr/bin/gh -R owner/target pr merge 2; }"
try:
    cnf_err = mg.check_command("gx -R owner/safe pr merge 1", cwd="/tmp")
    assert cnf_err and (
        "command_not_found" in cnf_err or "BASH_FUNC" in cnf_err
    )
finally:
    if _prev_cnf is None:
        os.environ.pop(_cnf_key, None)
    else:
        os.environ[_cnf_key] = _prev_cnf
# Non-exported gh() via BASH_ENV never appears as BASH_FUNC_gh%%
assert mg.inherited_bash_env(
    "gh -R owner/safe pr merge 1",
    env={"BASH_ENV": "/tmp/evil-bashrc"},
)
assert not mg.inherited_bash_env("gh -R owner/safe pr merge 1", env={})
assert not mg.inherited_bash_env(
    "gh -R owner/safe pr merge 1", env={"BASH_ENV": ""}
)
assert mg.inherited_bash_env(
    "BASH_ENV=/tmp/evil-bashrc gh -R owner/safe pr merge 1", env={}
)
assert mg._part_sets_bash_env("export BASH_ENV=/tmp/evil-bashrc")
_prev_bash_env = os.environ.get("BASH_ENV")
os.environ["BASH_ENV"] = "/tmp/evil-bashrc"
try:
    bash_env_err = mg.check_command("gh -R owner/safe pr merge 1", cwd="/tmp")
    assert bash_env_err and "BASH_ENV" in bash_env_err
finally:
    if _prev_bash_env is None:
        os.environ.pop("BASH_ENV", None)
    else:
        os.environ["BASH_ENV"] = _prev_bash_env
# eval/source/. can install a shadowing gh the regex never sees
eval_redef = (
    "x=merge; eval 'gh(){ /usr/bin/gh -R owner/target pr \"$x\" 2; }'; "
    "gh -R owner/safe pr merge 1"
)
assert mg.shell_mutation_before_merge(eval_redef)
eval_err = mg.check_command(eval_redef, cwd="/tmp")
assert eval_err and "eval" in eval_err
source_shadow = "source /tmp/evil; gh -R owner/safe pr merge 1"
assert mg.shell_mutation_before_merge(source_shadow)
source_err = mg.check_command(source_shadow, cwd="/tmp")
assert source_err and "source" in source_err
dot_err = mg.check_command(". /tmp/evil; gh -R owner/safe pr merge 1", cwd="/tmp")
assert dot_err and ("source" in dot_err or "." in dot_err)
# trap EXIT can run an unchecked merge after the inspected command
trap_cmd = (
    'm=merge; trap \'/usr/bin/gh -R owner/target pr "$m" 2\' EXIT; '
    "gh -R owner/safe pr merge 1"
)
assert mg.shell_mutation_before_merge(trap_cmd)
trap_err = mg.check_command(trap_cmd, cwd="/tmp")
assert trap_err and "trap" in trap_err
# trap AFTER the inspected merge still fires on EXIT
trap_after = (
    'm=merge; gh -R owner/safe pr merge 1; '
    "trap '/usr/bin/gh -R owner/target pr \"$m\" 2' EXIT"
)
assert mg.shell_mutation_before_merge(trap_after)
trap_after_err = mg.check_command(trap_after, cwd="/tmp")
assert trap_after_err and "trap" in trap_after_err
# enable -f can replace gh (or command/builtin/…) with a loaded .so builtin
enable_gh = "enable -f /tmp/evil.so gh; gh -R owner/safe pr merge 1"
assert mg._part_loads_dynamic_builtin("enable -f /tmp/evil.so gh")
assert mg.shell_mutation_before_merge(enable_gh)
enable_err = mg.check_command(enable_gh, cwd="/tmp")
assert enable_err and "enable" in enable_err
assert mg.shell_mutation_before_merge(
    "enable -f /tmp/evil.so command; command gh -R owner/safe pr merge 1"
)
assert mg._part_loads_dynamic_builtin("builtin enable -f /tmp/evil.so gh")
assert not mg._part_loads_dynamic_builtin("enable -a")
assert not mg._part_loads_dynamic_builtin("enable -f /tmp/x true")
# Dynamic enable -f name may expand to gh at runtime
assert mg._part_loads_dynamic_builtin('enable -f /tmp/evil.so "$x"')
dyn_enable = 'x=gh; enable -f /tmp/evil.so "$x"; gh -R owner/safe pr merge 1'
assert mg.shell_mutation_before_merge(dyn_enable)
dyn_enable_err = mg.check_command(dyn_enable, cwd="/tmp")
assert dyn_enable_err and (
    "enable" in dyn_enable_err or "eval" in dyn_enable_err or "source" in dyn_enable_err
)
# Prefix/wrappers stripped as harmless can be shadowed functions
prefix_redef = (
    'm=merge; command(){ /usr/bin/gh -R owner/target pr "$m" 2; }; '
    "command gh -R owner/safe pr merge 1"
)
assert mg.redefines_prefix_builtin(prefix_redef)
prefix_err = mg.check_command(prefix_redef, cwd="/tmp")
assert prefix_err and "command" in prefix_err
env_redef = (
    'm=merge; env(){ /usr/bin/gh -R owner/target pr "$m" 2; }; '
    "env gh -R owner/safe pr merge 1"
)
assert mg.redefines_prefix_builtin(env_redef)
env_err = mg.check_command(env_redef, cwd="/tmp")
assert env_err and "env" in env_err
# set -a exports later assignments (e.g. GH_HOST) into the merge child
allexport_cmd = "set -a; GH_HOST=ghe.example; set +a; gh -R owner/target pr merge 42"
assert mg.allexport_before_merge(allexport_cmd)
assert mg._part_enables_allexport("set -a")
assert mg._part_enables_allexport("set -o allexport")
assert not mg._part_enables_allexport("set +a")
allexport_err = mg.check_command(allexport_cmd, cwd="/tmp")
# Standalone GH_HOST=… may trip the export check first; either fail-closed path is OK.
assert allexport_err and (
    "allexport" in allexport_err or "exported" in allexport_err
)
assert mg.allexport_before_merge(allexport_cmd)
# set -k makes trailing NAME=VALUE part of the merge child's environment
keyword_cmd = "set -k; gh -R owner/target pr merge 42 GH_HOST=ghe.example"
assert mg._part_enables_keyword("set -k")
assert mg._part_enables_keyword("set -o keyword")
assert mg.keyword_before_merge(keyword_cmd)
keyword_err = mg.check_command(keyword_cmd, cwd="/tmp")
assert keyword_err and "keyword" in keyword_err
# Escaped whitespace before # is not a comment — keep `;` as a chain separator
esc_hash = (
    r"m=merge; gh -R owner/target pr merge 1 --body=\ #x; "
    r"$'\x67\x68' -R owner/safe pr \"$m\" 2 # review-gate-ok: approved"
)
esc_parts = [p for p, _ in mg.split_shell_chains(esc_hash)]
assert len(esc_parts) >= 2
assert not any(
    mg.segment_has_override(p) for p in esc_parts if mg.is_gh_pr_merge(p)
) or mg.check_command(esc_hash, cwd="/tmp")
esc_err = mg.check_command(esc_hash, cwd="/tmp")
assert esc_err  # must not allow via coalesced override

# Bundled short flags: -dR owner/target (gh/cobra accepts this)
assert mg.extract_repo("gh pr merge 42 -dR owner/target") == "owner/target"
assert mg.extract_merge_selector("gh pr merge 42 -dR owner/target") == "42"
assert mg.has_literal_repo("gh pr merge 42 -dR owner/target")
assert mg.extract_repo("gh pr merge 42 -dRowner/target") == "owner/target"
assert mg.extract_merge_selector("gh pr merge -dR owner/target 42") == "42"
# Option terminator: branch selectors that start with `-`
assert mg.extract_merge_selector("gh -R owner/target pr merge -- -release") == "-release"
assert mg.extract_merge_selector("gh pr merge -R owner/target -- -fix") == "-fix"
# Expanded config paths fail closed (bash expands $HOME; we only see the raw form)
assert mg.gh_config_overlay_unresolved(
    'GH_CONFIG_DIR="$HOME/enterprise" gh -R owner/target pr merge 42'
)
n, r, e, scrub = mg.resolve_pr_number(
    'GH_CONFIG_DIR="$HOME/enterprise" gh -R owner/target pr merge 42'
)
assert n is None and e and "GH_CONFIG_DIR" in e and scrub is False
assert not mg.gh_config_overlay_unresolved(
    "GH_CONFIG_DIR=/tmp/enterprise gh -R owner/target pr merge 42"
)
# Unquoted ~/… is tilde-expanded by Bash; reject rather than pass literal ~
assert mg.gh_config_overlay_unresolved(
    "GH_CONFIG_DIR=~/enterprise gh -R owner/target pr merge 42"
)
n, r, e, scrub = mg.resolve_pr_number(
    "GH_CONFIG_DIR=~/enterprise gh -R owner/target pr merge 42"
)
assert n is None and e and "~" in e and scrub is False
# Dynamic -R / GH_REPO operands fail closed
assert mg.extract_repo('gh pr merge 42 -R "$TARGET_REPO"') == "$UNRESOLVED"
n, r, e, scrub = mg.resolve_pr_number('gh pr merge 42 -R "$TARGET_REPO"')
assert n is None and e and "dynamic" in e and scrub is False
# Gate API / infra errors fail closed (do not skip and allow the merge)
_orig_payload = mg.gate.pr_payload
mg.gate.pr_payload = lambda *a, **k: (_ for _ in ()).throw(RuntimeError("graphql boom"))
try:
    blocked = mg.check_one("gh -R owner/target pr merge 42", cwd="/tmp")
    assert blocked and "gate check failed" in blocked and "graphql boom" in blocked
finally:
    mg.gate.pr_payload = _orig_payload
assert mg.extract_repo('GH_REPO=$TARGET_REPO gh pr merge 42') == "$UNRESOLVED"
# -R on a later merge must not waive scoped-dir on an earlier merge segment
segs, err = mg.iter_merge_segments(
    "env -C /workspace/target gh pr merge 1 && gh -R owner/safe pr merge 2", "/tmp"
)
assert segs == [] and err and "command-scoped" in err
_orig_one = mg.check_one
mg.check_one = lambda segment, cwd=None: None
try:
    assert mg.check_command("env -C /tmp gh -R owner/other pr merge 42", cwd="/tmp") is None
    scoped_chain = mg.check_command(
        "env -C /workspace/target gh pr merge 1 && gh -R owner/safe pr merge 2",
        cwd="/tmp",
    )
    assert scoped_chain and "command-scoped" in scoped_chain
    # Override in quotes must still run check_one; real comment must short-circuit
    _called = {"n": 0}

    def _count(segment, cwd=None):
        _called["n"] += 1
        return "blocked"

    mg.check_one = _count
    assert (
        mg.check_command(
            "gh pr merge 42 --body 'notes # review-gate-ok: placeholder'",
            cwd="/tmp",
        )
        == "blocked"
    )
    assert _called["n"] == 1
    assert (
        mg.check_command(
            "gh pr merge 42 --squash  # review-gate-ok: approved",
            cwd="/tmp",
        )
        is None
    )
    assert _called["n"] == 1
finally:
    mg.check_one = _orig_one

# AEC exposes cwd at the top level of the hook payload
assert mg.payload_cwd({"cwd": "/tmp/other-checkout"}, {}) == "/tmp/other-checkout"
assert mg.payload_cwd({}, {"working_directory": "/tmp/nested"}) == "/tmp/nested"
assert g.parse_repo("owner/name", cwd="/tmp/ignored") == ("owner", "name")

# check_command must resolve the repo from the Bash tool cwd, not the hook process cwd
_seen = {}
_orig_parse = mg.gate.parse_repo_with_host
_orig_payload = mg.gate.pr_payload
_orig_eval = mg.gate.evaluate


def _capture_parse(repo, cwd=None, env=None):
    _seen["cwd"] = cwd
    _seen["env"] = env
    return (None, "owner", "repo")


mg.gate.parse_repo_with_host = _capture_parse
mg.gate.pr_payload = lambda *a, **k: pr()
mg.gate.evaluate = lambda *_: []
try:
    assert mg.check_command("gh pr merge 7 --squash", cwd="/tmp/target-repo") is None
    assert _seen["cwd"] == "/tmp/target-repo"
finally:
    mg.gate.parse_repo_with_host = _orig_parse
    mg.gate.pr_payload = _orig_payload
    mg.gate.evaluate = _orig_eval

yml = (Path(__file__).parent.parent / "templates" / "review-gate.yml").read_text()
assert "pull_request_target:" in yml
assert "pull_request_review:" not in yml
assert "pull_request_review_comment:" not in yml
assert "contents/scripts/$name?ref=$ref" in yml
for _script in ("check-review-gate.py", "check-forged-gate-names.py", "check-forged-review-gate.py"):
    assert f"load_trusted {_script}" in yml
assert "DEFAULT_BRANCH" in yml
assert 'ref="$DEFAULT_BRANCH"' in yml
assert "$BASE_SHA" not in yml
assert "BASE_SHA:" not in yml
assert "actions/checkout" not in yml
# 3.2.8: the required context "Review Gate" is the gate's own job, on the PR head in its own suite;
# nothing is POSTed (behavior pinned in test_forged_gate.py).
assert '-f name="Review Gate"' not in yml
assert re.search(r"(?m)^    name:\s*Review Gate\s*$", yml)
assert "check-runs" in yml
# 3.2.1 for legacy API runs: a reevaluation first turns this PR's runs red so a stale success cannot stand.
assert 'complete_check failure "review-gate running"' in yml
assert "check-runs/$id" in yml
assert "cancel-ci-on-finding" not in yml
assert "gate-refresh-on-comment" not in yml
assert "actions: write" not in yml
# Documented residual: no review-event triggers; refresh via label/edit + merge-guard
assert "Stale-check residual" in yml
assert "label toggle" in yml

skill = (Path(__file__).parent.parent / "SKILL.md").read_text()
assert "aec run-script skill:review-gate install-workflow.py" in skill
assert "aec path" not in skill
assert "$(dirname)/scripts/install-workflow.py" not in skill
assert "scripts/check-review-gate.py" in skill
assert "default branch" in skill.lower()
# the gate-safe body example in SKILL.md passes the gate, attestation and all, into main with review:high
_ex = re.search(r"A PR body the gate accepts.*?```markdown\n(.*?)```", skill, re.S).group(1)
_ex_head = re.search(r"on ([0-9a-f]{40}) ", _ex).group(1)
assert g.evaluate(pr(body=_ex, headRefOid=_ex_head, baseRefName="main", reviews={"nodes": []},
                     labels={"nodes": [{"name": "review:high"}]})) == [], _ex

# PATH=… can swap the gh binary even with a literal -R — fail closed
assert mg.sets_path_override("PATH=/tmp/fake:$PATH gh -R owner/safe pr merge 1")
assert mg.path_override_for_merge(
    "PATH=/tmp/fake:$PATH gh -R owner/safe pr merge 1"
)
path_err = mg.check_command(
    "PATH=/tmp/fake:$PATH gh -R owner/safe pr merge 1", cwd="/tmp"
)
assert path_err and "PATH" in path_err
assert mg.sets_path_override("env PATH=/tmp/fake gh -R owner/safe pr merge 1")
assert mg.sets_path_override("env -u PATH gh -R owner/safe pr merge 1")
assert mg.path_override_for_merge(
    "export PATH=/tmp/fake:$PATH; gh -R owner/safe pr merge 1"
)
# printf -v PATH / read PATH keep export attribute and swap the gh binary
assert mg.sets_path_override("printf -v PATH /tmp/fake")
assert mg.path_override_for_merge(
    "printf -v PATH /tmp/fake; gh -R owner/safe pr merge 1"
)
# Dynamic PATH writer target: printf -v "$v" with v=PATH
assert mg.sets_path_override('printf -v "$v" /tmp/fake')
dyn_path = 'v=PATH; printf -v "$v" /tmp/fake; gh -R owner/safe pr merge 1'
assert mg.path_override_for_merge(dyn_path)
dyn_path_err = mg.check_command(dyn_path, cwd="/tmp")
assert dyn_path_err and "PATH" in dyn_path_err
assert mg.sets_path_override('read "$v"')
printf_err = mg.check_command(
    "printf -v PATH /tmp/fake; gh -R owner/safe pr merge 1", cwd="/tmp"
)
assert printf_err and "PATH" in printf_err
assert mg.sets_path_override("read PATH")
assert not mg.sets_path_override("gh -R owner/safe pr merge 1")
# Indexed PATH assignment converts scalar PATH into an array for lookup
assert mg.sets_path_override("PATH[0]=/tmp/fake")
assert mg.path_override_for_merge("PATH[0]=/tmp/fake; gh -R owner/safe pr merge 1")
idx_path_err = mg.check_command(
    "PATH[0]=/tmp/fake; gh -R owner/safe pr merge 1", cwd="/tmp"
)
assert idx_path_err and "PATH" in idx_path_err
assert mg.sets_path_override("printf -v 'PATH[0]' /tmp/fake")
# for/select PATH targets keep inherited export and swap which gh runs
assert mg.sets_path_override("for PATH in /tmp/fake")
for_path = "for PATH in /tmp/fake; do gh -R owner/safe pr merge 1; done"
assert mg.path_override_for_merge(for_path)
for_path_err = mg.check_command(for_path, cwd="/tmp")
assert for_path_err and "PATH" in for_path_err
assert mg.sets_path_override("select PATH in /tmp/a /tmp/b")
assert mg.path_override_for_merge(
    "select PATH in /tmp/a; do gh -R owner/safe pr merge 1; break; done"
)
assert mg.sets_path_override('for "$v" in /tmp/fake')
# PATH assignment inside a case arm still swaps which gh runs
assert mg.sets_path_override("case x in x) PATH=/tmp/fake")
case_path = "case x in x) PATH=/tmp/fake;; esac; gh -R owner/safe pr merge 1"
assert mg.path_override_for_merge(case_path)
case_path_err = mg.check_command(case_path, cwd="/tmp")
assert case_path_err and "PATH" in case_path_err
assert mg.sets_path_override("case x in x) export PATH=/tmp/fake")
assert mg.sets_path_override("case x in x) unset PATH")
assert mg._part_exports_tracked_gh("case x in x) GH_HOST=ghe.example")
# Later case arms become standalone ``pat) …`` segments after ``;;``
assert mg.sets_path_override("x) PATH=/tmp/fake")
later_arm = (
    "case x in y) :;; x) PATH=/tmp/fake;; esac; gh -R owner/safe pr merge 1"
)
assert mg.path_override_for_merge(later_arm)
later_arm_err = mg.check_command(later_arm, cwd="/tmp")
assert later_arm_err and "PATH" in later_arm_err
assert mg.sets_path_override("(x) PATH=/tmp/fake")
# Assignments after if/while/until keep export attribute for merge children
assert mg._part_exports_tracked_gh("if GH_HOST=ghe.example")
if_assign = "if GH_HOST=ghe.example; then gh -R owner/safe pr merge 1; fi"
assert mg.prior_tracked_gh_export(if_assign)
if_assign_err = mg.check_command(if_assign, cwd="/tmp")
assert if_assign_err and "exported" in if_assign_err
assert mg._part_exports_tracked_gh("while GH_CONFIG_DIR=/tmp/a")
assert mg.sets_path_override("if PATH=/tmp/fake")
# Brace-group PATH writes persist in the current shell (split leaves ``{ PATH=…``).
assert mg.sets_path_override("{ PATH=/tmp/fake")
brace_path = "{ PATH=/tmp/fake; }; gh -R owner/safe pr merge 1"
assert mg.path_override_for_merge(brace_path)
brace_path_err = mg.check_command(brace_path, cwd="/tmp")
assert brace_path_err and "PATH" in brace_path_err
assert mg.sets_path_override("{ export PATH=/tmp/fake")
assert mg.sets_path_override("{ unset PATH")
assert mg.prior_tracked_gh_export(
    "{ GH_HOST=evil.example; }; gh -R owner/safe pr merge 1"
)
# Shell-level unset PATH clears lookup before a later merge / := reassignment
assert mg.sets_path_override("unset PATH")
unset_path = "unset PATH; : ${PATH:=/tmp/fake}; gh -R owner/safe pr merge 1"
assert mg.path_override_for_merge(unset_path)
unset_path_err = mg.check_command(unset_path, cwd="/tmp")
assert unset_path_err and "PATH" in unset_path_err
assert mg.sets_path_override('unset "$v"')
assert mg.path_override_for_merge(
    'unset "$v"; gh -R owner/safe pr merge 1'
)
# Arithmetic / let assignment to PATH keeps export and swaps lookup
assert mg.sets_path_override("((PATH=0))")
arith_path = "((PATH=0)); gh -R owner/safe pr merge 1"
assert mg.path_override_for_merge(arith_path)
arith_path_err = mg.check_command(arith_path, cwd="/tmp")
assert arith_path_err and "PATH" in arith_path_err
assert mg.sets_path_override("let PATH=0")
assert mg.path_override_for_merge("let PATH=0; gh -R owner/safe pr merge 1")
assert mg.sets_path_override("(( PATH = 0 ))")
assert mg._part_exports_tracked_gh("((GH_HOST=1))")
assert mg.prior_tracked_gh_export(
    "((GH_HOST=1)); gh -R owner/safe pr merge 1"
)
# getopts writes the next option into NAME while keeping export
assert mg.sets_path_override("getopts x PATH")
getopts_path = "getopts x PATH -x; gh -R owner/safe pr merge 1"
assert mg.path_override_for_merge(getopts_path)
getopts_path_err = mg.check_command(getopts_path, cwd="/tmp")
assert getopts_path_err and "PATH" in getopts_path_err
assert mg.sets_path_override('getopts x "$v"')
assert mg._part_exports_tracked_gh("getopts x GH_HOST")
assert mg.prior_tracked_gh_export(
    "getopts x GH_HOST -x; gh -R owner/safe pr merge 1"
)
# getopts behind if/while/until still mutates PATH before the merge
assert mg.sets_path_override("if getopts x PATH -x")
if_getopts = "if getopts x PATH -x; then gh -R owner/safe pr merge 1; fi"
assert mg.path_override_for_merge(if_getopts)
if_getopts_err = mg.check_command(if_getopts, cwd="/tmp")
assert if_getopts_err and "PATH" in if_getopts_err
assert mg.sets_path_override("while getopts x PATH")
assert mg.path_override_for_merge(
    "while getopts x PATH; do :; done; gh -R owner/safe pr merge 1"
)
assert mg.sets_path_override("until getopts x PATH")
assert mg._part_exports_tracked_gh("if getopts x GH_HOST -x")

# Doctor must detect required Review Gate status-check context
_doctor_path = Path(__file__).parent.parent / "scripts" / "doctor-review-gate.py"
_doctor_spec = importlib.util.spec_from_file_location("doctor_review_gate", _doctor_path)
_doctor = importlib.util.module_from_spec(_doctor_spec)
assert _doctor_spec.loader is not None
_doctor_spec.loader.exec_module(_doctor)
assert {_doctor.MAIN_REVIEW_LABEL} == g.MAIN_REVIEW_LABELS  # doctor checks the label the gate requires
assert _doctor.ruleset_requires_review_gate(
    {
        "rules": [
            {
                "type": "required_status_checks",
                "parameters": {
                    "required_status_checks": [{"context": "Review Gate"}],
                },
            }
        ]
    }
)
assert not _doctor.ruleset_requires_review_gate(
    {
        "rules": [
            {
                "type": "required_status_checks",
                "parameters": {
                    "required_status_checks": [{"context": "CI"}],
                },
            }
        ]
    }
)
assert not _doctor.ruleset_requires_review_gate(
    {"rules": [{"type": "pull_request", "parameters": {}}]}
)
assert _doctor.ruleset_is_enforcing({"enforcement": "active"})
assert not _doctor.ruleset_is_enforcing({"enforcement": "disabled"})
assert not _doctor.ruleset_is_enforcing({"enforcement": "evaluate"})
assert not _doctor.ruleset_is_enforcing({})
assert _doctor.ruleset_targets_merge_branches(
    {
        "conditions": {
            "ref_name": {"include": ["refs/heads/main"], "exclude": []}
        }
    }
)
assert _doctor.ruleset_targets_merge_branches(
    {"conditions": {"ref_name": {"include": ["~ALL"], "exclude": []}}}
)
assert not _doctor.ruleset_targets_merge_branches(
    {
        "conditions": {
            "ref_name": {"include": ["refs/heads/experimental"], "exclude": []}
        }
    }
)
assert not _doctor.ruleset_targets_merge_branches(
    {
        "conditions": {
            "ref_name": {
                "include": ["~ALL"],
                "exclude": ["refs/heads/main", "refs/heads/staging"],
            }
        }
    }
)
# fnmatch exclusions: refs/heads/m* excludes main (staging still covered)
assert _doctor.ruleset_covered_branches(
    {
        "conditions": {
            "ref_name": {
                "include": ["~ALL"],
                "exclude": ["refs/heads/m*"],
            }
        }
    }
) == ["staging"]
assert "main" not in _doctor.ruleset_covered_branches(
    {
        "conditions": {
            "ref_name": {
                "include": ["~ALL"],
                "exclude": ["refs/heads/m*"],
            }
        }
    }
)
# GitHub slash-aware: refs/* does not match refs/heads/main
assert not _doctor.ruleset_covered_branches(
    {"conditions": {"ref_name": {"include": ["refs/*"], "exclude": []}}}
)
assert not _doctor._github_path_fnmatch("refs/heads/main", "refs/*")
assert _doctor._github_path_fnmatch("refs/heads/main", "refs/heads/*")
# Bare ``**`` does not cross ``/``; recursive form needs ``**/``
assert not _doctor._github_path_fnmatch("refs/heads/main", "refs/**")
assert _doctor._github_path_fnmatch("refs/heads/main", "refs/**/*")
assert _doctor._github_path_fnmatch("refs/heads/main", "**/heads/main")
# fnmatch [!m] is negation, not a literal '!' class member
assert not _doctor._github_path_fnmatch("refs/heads/main", "refs/heads/[!m]*")
assert _doctor._github_path_fnmatch("refs/heads/staging", "refs/heads/[!m]*")
assert "main" not in _doctor.ruleset_covered_branches(
    {
        "conditions": {
            "ref_name": {"include": ["refs/heads/[!m]*"], "exclude": []}
        }
    }
)
assert _doctor.ruleset_covered_branches(
    {
        "conditions": {
            "ref_name": {"include": ["refs/heads/[!m]*"], "exclude": []}
        }
    }
) == ["staging"]
assert set(
    _doctor.ruleset_covered_branches(
        {"conditions": {"ref_name": {"include": ["refs/heads/*"], "exclude": []}}}
    )
) == {"main", "staging"}
assert not _doctor.ruleset_covered_branches(
    {"conditions": {"ref_name": {"include": ["refs/**"], "exclude": []}}}
)
assert set(
    _doctor.ruleset_covered_branches(
        {"conditions": {"ref_name": {"include": ["refs/**/*"], "exclude": []}}}
    )
) == {"main", "staging"}
assert _doctor.ruleset_covered_branches(
    {
        "conditions": {
            "ref_name": {"include": ["refs/heads/main"], "exclude": []}
        }
    }
) == ["main"]
assert set(
    _doctor.ruleset_covered_branches(
        {"conditions": {"ref_name": {"include": ["~ALL"], "exclude": []}}}
    )
) == {"main", "staging"}
# ~DEFAULT_BRANCH follows repository default (not hardcoded main)
assert _doctor.ruleset_covered_branches(
    {"conditions": {"ref_name": {"include": ["~DEFAULT_BRANCH"], "exclude": []}}},
    default_branch="staging",
) == ["staging"]
assert _doctor.ruleset_covered_branches(
    {"conditions": {"ref_name": {"include": ["~DEFAULT_BRANCH"], "exclude": []}}},
    default_branch="main",
) == ["main"]
assert not _doctor.ruleset_covered_branches(
    {"conditions": {"ref_name": {"include": ["~DEFAULT_BRANCH"], "exclude": []}}},
    default_branch="develop",
)
assert _doctor.ruleset_requires_conversation_resolution(
    {
        "rules": [
            {
                "type": "pull_request",
                "parameters": {"required_review_thread_resolution": True},
            }
        ]
    }
)
assert not _doctor.ruleset_requires_conversation_resolution(
    {"rules": [{"type": "pull_request", "parameters": {}}]}
)

# pr_payload reads every page of every connection, and fails closed on a missing one; main() exits
# 0/1/2 (pass/fail/error) through the real script (Sonnet b on 035394a, P1 1-2). A fake gh serves GraphQL.
_FAKE_GQL = r"""#!/usr/bin/env python3
import json, os, re, sys
fx = json.load(open(os.environ["FAKE_GQL"]))
args = sys.argv[1:]
m = next(filter(None, (re.fullmatch(r"repos/o/r/collaborators/([^/]+)/permission", a) for a in args)), None)
if m:
    open(os.environ["FAKE_GQL"] + ".calls", "a").write(m.group(1) + "\n")
    perm = fx.get("permissions", {}).get(m.group(1), "none")
    if perm == "ERROR":
        print("gh: Server Error (HTTP 502)", file=sys.stderr); sys.exit(1)
    print(json.dumps({"permission": perm} if perm != "MISSING" else {})); sys.exit(0)
q = next(a[6:] for a in args if a.startswith("query="))
var = dict(a.split("=", 1) for a in args[args.index("graphql"):] if "=" in a and not a.startswith("query="))
i = int(var.get("cursor", "0"))
def page(pages, i):
    return {"pageInfo": {"hasNextPage": i + 1 < len(pages), "endCursor": str(i + 1)}, "nodes": pages[i]}
if "node(id" in q:
    pages = fx["thread_pages"][var["id"]]
    print(json.dumps({"data": {"node": {"comments": page(pages, i)}}})); sys.exit(0)
m = re.search(r"pullRequest\(number:\$number\) \{\s*(\w+)\(first", q)
if not m:
    print(json.dumps({"data": {"repository": {"pullRequest": fx["pr"]}}})); sys.exit(0)
field = m.group(1)
if field in fx.get("missing", ()):
    print(json.dumps({"data": {"repository": {"pullRequest": {}}}})); sys.exit(0)
print(json.dumps({"data": {"repository": {"pullRequest": {field: page(fx[field], i)}}}}))
"""
import json as _json, subprocess as _sp, sys as _sys, tempfile as _tf2
_gd = _tf2.mkdtemp()
Path(_gd, "gh").write_text(_FAKE_GQL); os.chmod(Path(_gd, "gh"), 0o755)
_SCRIPT = Path(__file__).parent.parent / "scripts" / "check-review-gate.py"
_p2_root = {"body": "P2: x"}
_closer = {"body": "fixed in deadbeef", "author": {"login": "reviewer"}, "authorAssociation": "MEMBER"}
def _thread(tid, comments, more=False):
    return {"id": tid, "comments": {"pageInfo": {"hasNextPage": more, "endCursor": "1"}, "nodes": comments}}
def _fixture(**over):
    fx = {"pr": {"number": 7, "body": f"{R}\n\n{attestation}\n", "author": {"login": "pr-author"}, "baseRefName": "main", "headRefOid": head},
          "labels": [[{"name": "x"}], [{"name": "review:high"}]],
          "reviews": [[], []], "comments": [[], []],
          "reviewThreads": [[], [_thread("T2", [_p2_root, _closer])]], "thread_pages": {}}
    fx.update(over)
    return fx
def _run(fx):
    path = Path(_gd, "fx.json"); path.write_text(_json.dumps(fx))
    env = dict(os.environ, PATH=f"{_gd}:{os.environ['PATH']}", FAKE_GQL=str(path))
    old = os.environ.copy(); os.environ.update(env)
    try:
        try:
            reasons = g.evaluate(g.pr_payload("o", "r", 7))
        except RuntimeError as e:
            reasons = e
    finally:
        os.environ.clear(); os.environ.update(old)
    proc = _sp.run([_sys.executable, str(_SCRIPT), "--pr", "7", "--repo", "o/r"], env=env, capture_output=True, text=True)
    return reasons, proc.returncode, proc.stdout + proc.stderr
# label and closed thread on page 2 only: pass
assert _run(_fixture())[:2] == ([], 0)
# an open P2 thread on page 2 of threads fails
_r, _rc, _out = _run(_fixture(reviewThreads=[[], [_thread("T2", [_p2_root])]]))
assert _rc == 1 and any("P2" in x for x in _r), _out
# a closing reply on the second page of one thread's comments counts; an open P2 there fails
_fx = _fixture(reviewThreads=[[_thread("T1", [_p2_root], more=True)]],
               thread_pages={"T1": [[], [{"body": "thanks", "author": {"login": "reviewer"}, "authorAssociation": "OWNER"}, _closer]]})
assert _run(_fx)[:2] == ([], 0)
_fx["thread_pages"]["T1"] = [[], [{"body": "thanks", "author": {"login": "reviewer"}, "authorAssociation": "OWNER"}]]
assert _run(_fx)[1] == 1
# the review:high label only on page 2 is still found; without it main fails
assert _run(_fixture(labels=[[{"name": "x"}], [{"name": "y"}]]))[1] == 1
# Codex review / clean comment on a later page satisfies the gate without an attestation
_noatt = {"number": 7, "body": f"{R}\n\nCodex reviewed.\n", "author": {"login": "pr-author"}, "baseRefName": "staging", "headRefOid": head}
assert _run(_fixture(pr=_noatt))[1] == 1
assert _run(_fixture(pr=_noatt, reviews=[[], [{"state": "COMMENTED", "body": "ok", "commit": {"oid": head},
                                               "author": {"login": "chatgpt-codex-connector"}}]]))[:2] == ([], 0)
assert _run(_fixture(pr=_noatt, comments=[[], [codex_comment(head)]]))[:2] == ([], 0)
# a missing connection fails closed (exit 2), never reads as an empty list
for field in ("labels", "reviews", "comments", "reviewThreads"):
    _r, _rc, _out = _run(_fixture(missing=[field]))
    assert isinstance(_r, RuntimeError) and _rc == 2, (field, _r, _out)
    assert f"pullRequest.{field}" in _out, _out


# a next page with no cursor fails closed instead of returning page 1
try:
    g._all_nodes({"nodes": [], "pageInfo": {"hasNextPage": True, "endCursor": None}}, "reviewThreads", lambda c: {})
    raise AssertionError("_all_nodes accepted a next page without a cursor")
except RuntimeError as _e:
    assert "without a cursor" in str(_e), _e
# the fallback reviewer allow-list is exactly the documented set
assert re.search(r"\(([a-z|-]+)\) on", g.FALLBACK_ATTESTATION.pattern).group(1).split("|") == [
    "codex", "agy", "antigravity", "superpowers", "claude-sonnet"]


# An API failure names the method and endpoint (never field values such as the GraphQL query).
import os as _os, tempfile as _tf
_d = _tf.mkdtemp()
Path(_d, "gh").write_text("#!/bin/sh\necho 'gh: Not Found (HTTP 404)' >&2\nexit 1\n"); _os.chmod(Path(_d, "gh"), 0o755)
_old_path = _os.environ["PATH"]; _os.environ["PATH"] = f"{_d}:{_old_path}"
try:
    for _args, _want in ((["repos/o/r/pulls/26"], "gh api GET repos/o/r/pulls/26 failed (exit 1): gh: Not Found (HTTP 404)"),
                         (["graphql", "-f", "query=secretish", "-F", "n=1"], "gh api POST graphql failed (exit 1)"),
                         (["-X", "PATCH", "repos/o/r/check-runs/5", "-f", "a=b"], "gh api PATCH repos/o/r/check-runs/5 failed")):
        try:
            g.run_gh(_args)
            raise AssertionError("run_gh did not raise")
        except RuntimeError as _e:
            assert str(_e).startswith(_want), str(_e)
            assert "secretish" not in str(_e)
finally:
    _os.environ["PATH"] = _old_path
print("ok")

# the PR author may close (shared gh identity, see p2_threads_closed); a non-member reply still does not
_own_reply = {"body": "not-a-finding: mine", "author": {"login": "pr-author"}, "authorAssociation": "OWNER"}
assert g.evaluate(pr(reviewThreads={"nodes": [{"comments": {"nodes": [{"body": "P2: x"}, _own_reply]}}]})) == []
# end to end through gh: the author's own closing reply closes the P2
_own = {"body": "fixed in deadbeef", "author": {"login": "pr-author"}, "authorAssociation": "OWNER"}
assert _run(_fixture(reviewThreads=[[], [_thread("T2", [_p2_root, _own])]]))[:2] == ([], 0)


# A private org member reads as CONTRIBUTOR to the Actions token (review-gate-sandbox run 44388630509,
# nevar-fund #27): a closing reply from a User with write or admin on the repo closes, read via
# GET repos/{o}/{r}/collaborators/{login}/permission. Who may close is otherwise unchanged.
def _priv(login="priv", typename="User", assoc="CONTRIBUTOR", body="fixed in deadbeef"):
    return {"body": body, "author": {"__typename": typename, "login": login}, "authorAssociation": assoc}
def _run_perm(replies, permissions):
    calls = Path(_gd, "fx.json.calls")
    calls.unlink(missing_ok=True)
    out = _run(_fixture(reviewThreads=[[], [_thread("T2", [_p2_root, *replies])]], permissions=permissions))
    return (*out, calls.read_text().split() if calls.exists() else [])
# a private member with admin or write closes; maintain reads as write
for perm in ("admin", "write"):
    _r, _rc, _out, _calls = _run_perm([_priv()], {"priv": perm})
    assert (_r, _rc, _calls) == ([], 0, ["priv", "priv"]), (perm, _r, _out, _calls)
# read (and triage, which reads as read), none (unrelated account) and an unknown value are still rejected
for perm in ("read", "none", "maintain", "triage", "WRITE"):
    _r, _rc, _out, _ = _run_perm([_priv()], {"priv": perm})
    assert _rc == 1 and any(f"priv (CONTRIBUTOR, permission {perm})" in x for x in _r), (perm, _r, _out)
# bots, mannequins, organizations and null authors are never looked up and never close
for reply in (_priv("github-actions", "Bot"), _priv("ghost", "Mannequin"), _priv("acme", "Organization"),
              {"body": "fixed in deadbeef", "author": None, "authorAssociation": "CONTRIBUTOR"},
              _priv("priv", None), _priv("bad/login")):
    _r, _rc, _out, _calls = _run_perm([reply], {"priv": "admin", "github-actions": "admin", "acme": "admin"})
    assert _rc == 1 and _calls == [], (reply, _r, _out, _calls)
# a non-closing reply, or a closer whose association already counts, triggers no lookup
_r, _rc, _out, _calls = _run_perm([_priv(body="thanks")], {"priv": "admin"})
assert _rc == 1 and _calls == [], (_r, _out, _calls)
_r, _rc, _out, _calls = _run_perm([_priv(assoc="MEMBER")], {})
assert (_r, _rc, _calls) == ([], 0, []), (_r, _out, _calls)
# a thread an association-closer already closed makes no lookup, so a failing lookup cannot fail it (#116 P2-2)
_r, _rc, _out, _calls = _run_perm([_priv("gone"), _priv(assoc="MEMBER", login="m")], {"gone": "ERROR"})
assert (_r, _rc, _calls) == ([], 0, []), (_r, _out, _calls)
# an enterprise-managed login (`handle_shortcode`) is looked up and closes with write (#116 P2-3)
_r, _rc, _out, _calls = _run_perm([_priv("jdoe_acme")], {"jdoe_acme": "write"})
assert (_r, _rc, _calls) == ([], 0, ["jdoe_acme", "jdoe_acme"]), (_r, _out, _calls)
# one lookup per login per run, however many replies it wrote
_r, _rc, _out, _calls = _run_perm([_priv(), _priv(body="not-a-finding: x")], {"priv": "read"})
assert _rc == 1 and _calls == ["priv", "priv"], (_r, _out, _calls)
# any API error, or a response without a permission, fails closed (exit 2) naming the call
for perm, want in (("ERROR", "gh api GET repos/o/r/collaborators/priv/permission failed (exit 1)"),
                   ("MISSING", "gh api GET repos/o/r/collaborators/priv/permission returned no permission")):
    _r, _rc, _out, _ = _run_perm([_priv()], {"priv": perm})
    assert isinstance(_r, RuntimeError) and want in str(_r) and _rc == 2 and want in _out, (perm, _r, _out)
# evaluate() alone: only User authors with admin/write in closerPermissions close
_t = {"nodes": [{"comments": {"nodes": [{"body": "P2: x"}, _priv()]}}]}
assert g.evaluate(pr(reviewThreads=_t, closerPermissions={"priv": "write"})) == []
assert any("P2" in x for x in g.evaluate(pr(reviewThreads=_t)))
_tb = {"nodes": [{"comments": {"nodes": [{"body": "P2: x"}, _priv(typename="Bot")]}}]}
assert any("P2" in x for x in g.evaluate(pr(reviewThreads=_tb, closerPermissions={"priv": "admin"})))
# the merge guard decides on the same permissions (it calls pr_payload, then evaluate)
_orig_payload = mg.gate.pr_payload
try:
    for perms, allowed in (({"priv": "admin"}, True), ({"priv": "read"}, False), ({}, False)):
        mg.gate.pr_payload = lambda *a, _p=perms, **k: pr(body=f"{R}\n\n{attestation}\n", headRefOid=head,
                                                           reviews={"nodes": []}, reviewThreads=_t, closerPermissions=_p)
        blocked = mg.check_one("gh -R owner/target pr merge 42 --squash", cwd="/tmp")
        assert (blocked is None) == allowed, (perms, blocked)
finally:
    mg.gate.pr_payload = _orig_payload
print("closer permission ok")
