"""Run: python3 review-gate/tests/test_lint_review_body.py"""
import importlib.util
import subprocess
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"
LINTER = SCRIPTS / "lint-review-body.py"


def _load(name, file):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / file)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


g = _load("check_review_gate", "check-review-gate.py")
HEAD = "0123456789abcdef0123456789abcdef01234567"
ATT = f"Fallback review: claude-sonnet on {HEAD} — verdict: clean"
OK = f"## Summary\n\n- a list, `code` and [a link](https://x.y) are fine here\n\n## Review\n\n{ATT}\nTwo P2s were fixed.\n\n## Notes\n\n- footer\n"


def body(review_line=None, top=None):
    """Body with one extra line in ## Review (line 6) or above it (line 3)."""
    return (f"Summary\n\n{top}\n\n" if top is not None else "Summary\n\n") + "## Review\n\n" + ATT + "\n" + \
        (f"{review_line}\n" if review_line is not None else "")


def lint_cli(text):
    r = subprocess.run([sys.executable, str(LINTER)], input=text, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def gate_body_reasons(text):
    """What the gate itself says about this body, with the attestation and label satisfied."""
    reasons = g.evaluate({"body": text, "headRefOid": HEAD, "baseRefName": "main", "reviews": {"nodes": []},
                          "labels": {"nodes": [{"name": "review:high"}]}, "reviewThreads": {"nodes": []}})
    return reasons


# a valid body passes, by file, by stdin and by "-"
rc, out = lint_cli(OK)
assert rc == 0 and "OK" in out, out
assert gate_body_reasons(OK) == []
with __import__("tempfile").NamedTemporaryFile("w", suffix=".md", delete=False) as f:
    f.write(OK)
assert subprocess.run([sys.executable, str(LINTER), f.name], capture_output=True).returncode == 0
assert subprocess.run([sys.executable, str(LINTER), "-"], input=OK, capture_output=True, text=True).returncode == 0
assert subprocess.run([sys.executable, str(LINTER), "a", "b"], capture_output=True).returncode == 2
# an unreadable or non-UTF-8 file is a usage error (2) naming the path, not a traceback or a lint failure (1)
with __import__("tempfile").TemporaryDirectory() as d:
    (Path(d) / "latin1.md").write_bytes(b"## Review\n\ncaf\xe9\n")
    for path in (Path(d) / "missing.md", Path(d), Path(d) / "latin1.md"):
        r = subprocess.run([sys.executable, str(LINTER), str(path)], capture_output=True, text=True)
        assert r.returncode == 2 and "cannot read" in r.stderr and "Traceback" not in r.stderr, (path, r.stderr)

# every banned construct in ## Review fails on its own line (line 5 + 1 = 6 here), naming it
REVIEW_BAD = {
    "- a bullet": "starts with '-'",
    "* a bullet": "starts with '*'",
    "+ a bullet": "starts with '+'",
    "1. ordered": "ordered-list marker",
    "2) ordered": "ordered-list marker",
    "> a quote": "starts with '>'",
    " leading space": "starts with ' '",
    "## Reviews heading": None,  # a later `## ` line ends the region: not a failure
}
for ch in "`<>|[]()*_~$":
    REVIEW_BAD[f"Fixed the{ch}thing"] = f"character {ch!r} at column 10"
for line, want in REVIEW_BAD.items():
    text = body(line)
    rc, out = lint_cli(text)
    if want is None:
        assert rc == 0, (line, out)
        continue
    assert rc == 1 and "PR body line 6:" in out and want in out, (line, out)

# whole-body bans fail anywhere, above ## Review too (line 3)
TOP_BAD = {
    "```": "code fences",
    "  ~~~python": "code fences",
    "see <!-- hidden": "HTML comments",
    "<div>": "raw HTML",
    "- <b>x</b>": "raw HTML",
    "> <pre>": "raw HTML",
    "text <details> x": "<details>",
    "<DETAILS open>": "<details>",
}
for line, want in TOP_BAD.items():
    rc, out = lint_cli(body(top=line))
    assert rc == 1 and "PR body line 3:" in out and want in out, (line, out)

# structure: no heading, two headings, heading not after a blank line
for text, want in (("Summary\n", "found 0"), ("## Review\n\nx\n\n## Review\n", "found 2"),
                   ("Summary\n## Review\n", "line 2: '## Review' must follow a blank line")):
    rc, out = lint_cli(text)
    assert rc == 1 and want in out, (text, out)

# parity: on every fixture the linter's problems are exactly the gate's body reasons, and the linter passes
# a body exactly when the gate passes it (attestation and label satisfied), so drift fails CI
lint = _load("lint_review_body", "lint-review-body.py")
fixtures = [OK, body(), *(body(l) for l in REVIEW_BAD), *(body(top=l) for l in TOP_BAD),
            "Summary\n", "## Review\n\nx\n\n## Review\n", "Summary\n## Review\n", "Summary\r\n\r\n## Review\r\n\r\n" + ATT]
for text in fixtures:
    problems = lint.lint(text)
    reasons = gate_body_reasons(text)
    assert set(problems) == {r for r in reasons if r.startswith("PR body")}, (text, problems, reasons)
    assert (problems == []) == (reasons == []), (text, problems, reasons)
    rc, out = lint_cli(text)
    assert rc == (1 if problems else 0) and all(p in out for p in problems), (text, out)

# the linter has no grammar of its own: it reaches the checker's review_region
src = LINTER.read_text()
assert "review_region" in src and "re.compile" not in src and "import re" not in src
print("lint ok")
