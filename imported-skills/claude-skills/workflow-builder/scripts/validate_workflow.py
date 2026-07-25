#!/usr/bin/env python3
"""Linter for Claude Code workflow (.js) files.

Catches the parser-fatal and resume-breaking mistakes before a workflow runs:
meta-block rules, banned non-deterministic calls, forbidden Node/FS access in
the orchestrator, parallel()-needs-thunks, unguarded loops, and the script-size
cap. Reports PASS / WARN / FAIL with line numbers.

Stdlib only. Heuristic (regex/text) — it does not execute the file.
"""
import argparse
import re
import sys

MAX_SCRIPT_BYTES = 524_288
AGENT_CAP = 1000

# (severity, label) constants
FAIL, WARN, PASS = "FAIL", "WARN", "PASS"


def _strip_comments(src):
    """Remove // line and /* */ block comments so they don't trip pattern checks.
    Keeps line count stable by preserving newlines."""
    out = []
    i, n = 0, len(src)
    in_line = in_block = in_str = False
    str_ch = ""
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if in_line:
            if c == "\n":
                in_line = False
                out.append(c)
            else:
                out.append(" ")
            i += 1
        elif in_block:
            if c == "*" and nxt == "/":
                in_block = False
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_str:
            out.append(c)
            if c == "\\":
                if nxt:
                    out.append(nxt)
                    i += 2
                    continue
            elif c == str_ch:
                in_str = False
            i += 1
        else:
            if c == "/" and nxt == "/":
                in_line = True
                out.append("  ")
                i += 2
            elif c == "/" and nxt == "*":
                in_block = True
                out.append("  ")
                i += 2
            elif c in "\"'`":
                in_str = True
                str_ch = c
                out.append(c)
                i += 1
            else:
                out.append(c)
                i += 1
    return "".join(out)


def _lineno(src, idx):
    return src.count("\n", 0, idx) + 1


def check_size(raw, findings):
    n = len(raw.encode("utf-8"))
    if n > MAX_SCRIPT_BYTES:
        findings.append((FAIL, None, f"Script is {n} bytes, over the {MAX_SCRIPT_BYTES}-byte cap (rejected before parsing)."))


def check_meta(code, findings):
    m = re.search(r"export\s+const\s+meta\s*=", code)
    if not m:
        findings.append((FAIL, None, "No `export const meta = {...}` declaration found (required, must be first statement)."))
        return
    # meta should be the first non-empty, non-import statement.
    head = code[:m.start()]
    head_sig = re.sub(r"^\s*import\b.*$", "", head, flags=re.MULTILINE).strip()
    if head_sig:
        findings.append((WARN, _lineno(code, m.start()),
                         "`meta` may not be the first statement — move it above all other code (imports are allowed before it)."))
    # Extract the meta object body (balanced braces).
    brace_start = code.find("{", m.end())
    if brace_start == -1:
        findings.append((FAIL, _lineno(code, m.start()), "`meta` is not an object literal."))
        return
    depth, j = 0, brace_start
    while j < len(code):
        if code[j] == "{":
            depth += 1
        elif code[j] == "}":
            depth -= 1
            if depth == 0:
                break
        j += 1
    body = code[brace_start:j + 1]
    ln = _lineno(code, brace_start)
    if "name" not in body:
        findings.append((FAIL, ln, "`meta` is missing the required `name` field."))
    if "description" not in body:
        findings.append((FAIL, ln, "`meta` is missing the required `description` field."))
    # Pure-literal rule: no template strings, spreads, or function calls inside meta.
    if "`" in body:
        findings.append((FAIL, ln, "`meta` contains a template string — it must be a pure literal (use plain quoted strings)."))
    if "..." in body:
        findings.append((FAIL, ln, "`meta` contains a spread (`...`) — it must be a pure literal."))
    # function call: an identifier immediately followed by ( that isn't a key.
    if re.search(r"[A-Za-z_$][\w$]*\s*\(", body):
        findings.append((FAIL, ln, "`meta` contains a function call — it must be a pure literal (no variables or calls)."))
    for reserved in ("__proto__", "constructor", "prototype"):
        if reserved in body:
            findings.append((FAIL, ln, f"`meta` uses reserved key `{reserved}` (rejected by the parser)."))


def check_nondeterminism(code, findings):
    for pat, msg in [
        (r"\bMath\.random\s*\(", "Math.random() is banned (non-reproducible, breaks resume) — vary the prompt by index instead."),
        (r"\bDate\.now\s*\(", "Date.now() is banned (breaks resume) — pass timestamps via `args`."),
        (r"\bnew\s+Date\s*\(\s*\)", "argless `new Date()` is banned (breaks resume) — use `new Date(specificValue)` or pass via `args`."),
    ]:
        for m in re.finditer(pat, code):
            findings.append((FAIL, _lineno(code, m.start()), msg))


def check_node_apis(code, findings):
    for pat, msg in [
        (r"\brequire\s*\(", "`require(...)` is unavailable in the orchestrator — do this work inside an agent() call."),
        (r"\bimport\s+.*\bfrom\s+['\"]fs['\"]", "filesystem access is unavailable in the orchestrator — move it inside an agent()."),
        (r"\bprocess\.\w+", "`process.*` is unavailable in the orchestrator — move it inside an agent()."),
        (r"\bfs\.\w+\s*\(", "`fs.*` filesystem calls are unavailable in the orchestrator — move it inside an agent()."),
        (r"\bfetch\s*\(", "network `fetch(...)` is unavailable in the orchestrator — move it inside an agent()."),
    ]:
        for m in re.finditer(pat, code):
            findings.append((FAIL, _lineno(code, m.start()), msg))


def check_parallel_thunks(code, findings):
    """parallel(...) elements must be thunks: () => ... , not bare agent(...) promises."""
    for m in re.finditer(r"\bparallel\s*\(", code):
        # Look at the slice right after the opening paren up to a reasonable window.
        start = m.end()
        window = code[start:start + 400]
        # Common correct forms contain `=>` ; bare-promise misuse is parallel([agent(...) , ...]) or .map(x => agent(...)) without the extra thunk.
        # Flag .map(...) that returns agent(...) directly without `() =>`.
        if re.search(r"\.map\s*\(\s*\([^)]*\)\s*=>\s*agent\s*\(", window):
            findings.append((WARN, _lineno(code, m.start()),
                             "parallel(items.map(x => agent(...))) passes promises, not thunks — wrap as `x => () => agent(...)`."))
        elif re.search(r"\[\s*agent\s*\(", window):
            findings.append((WARN, _lineno(code, m.start()),
                             "parallel([ agent(...) , ... ]) passes bare promises — use thunks: `[() => agent(...), ...]`."))


def check_loops_guarded(code, findings):
    """Every while/for loop should reference a counter bound or budget.remaining()."""
    for m in re.finditer(r"\bwhile\s*\(([^)]*)\)", code):
        cond = m.group(1)
        ln = _lineno(code, m.start())
        if "true" in cond and "budget" not in cond:
            findings.append((WARN, ln, "`while (true)` loop — add a counter or budget.remaining() guard or it hits the 1000-agent cap."))
        elif "budget" not in cond and not re.search(r"[<>]=?|!==?|===?", cond):
            findings.append((WARN, ln, "loop condition has no obvious bound — confirm a counter cap or budget guard exists."))


def check_filter_boolean(code, findings):
    """Soft reminder: results of parallel/pipeline should be filtered for nulls before use."""
    uses_orchestration = re.search(r"\b(parallel|pipeline)\s*\(", code)
    if uses_orchestration and "filter(Boolean)" not in code and ".filter(" not in code:
        findings.append((WARN, None,
                         "No `.filter(Boolean)` found — skipped/failed agents insert `null`; filter results before using them."))


def check_agent_present(code, findings):
    if not re.search(r"\bagent\s*\(", code):
        findings.append((WARN, None, "No `agent(...)` calls found — a workflow with no sub-agents may not need to be a workflow."))


def validate(raw):
    findings = []
    check_size(raw, findings)
    code = _strip_comments(raw)
    check_meta(code, findings)
    check_nondeterminism(code, findings)
    check_node_apis(code, findings)
    check_parallel_thunks(code, findings)
    check_loops_guarded(code, findings)
    check_filter_boolean(code, findings)
    check_agent_present(code, findings)
    return findings


def verdict(findings):
    if any(f[0] == FAIL for f in findings):
        return FAIL
    if any(f[0] == WARN for f in findings):
        return WARN
    return PASS


def render(findings, path):
    v = verdict(findings)
    icon = {FAIL: "FAIL", WARN: "WARN", PASS: "PASS"}[v]
    lines = [f"[{icon}] {path}"]
    if not findings:
        lines.append("  No issues found. Workflow looks structurally valid.")
    for sev, ln, msg in sorted(findings, key=lambda f: (f[0] != FAIL, f[1] or 0)):
        loc = f"line {ln}" if ln else "file"
        lines.append(f"  {sev} ({loc}): {msg}")
    return "\n".join(lines)


SAMPLE = """export const meta = {
  name: 'bad-example',
  description: `template strings not allowed`,
}

const ts = Date.now()
while (true) {
  const r = await parallel([agent('find a bug')])
  bugs.push(...r)
}
"""


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("path", nargs="?", help="path to a workflow .js file")
    p.add_argument("--json", action="store_true", help="emit JSON findings")
    p.add_argument("--sample", action="store_true", help="lint a built-in intentionally-broken sample")
    args = p.parse_args(argv)

    if args.sample or not args.path:
        if not args.path and not args.sample:
            print("No path given; linting built-in --sample. Use --help for options.\n", file=sys.stderr)
        raw, label = SAMPLE, "<sample>"
    else:
        try:
            with open(args.path, "r", encoding="utf-8") as fh:
                raw = fh.read()
        except OSError as e:
            print(f"Could not read {args.path}: {e}", file=sys.stderr)
            return 2
        label = args.path

    findings = validate(raw)
    if args.json:
        import json
        print(json.dumps({
            "path": label,
            "verdict": verdict(findings),
            "findings": [{"severity": s, "line": ln, "message": m} for s, ln, m in findings],
        }, indent=2))
    else:
        print(render(findings, label))
    return 1 if verdict(findings) == FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
