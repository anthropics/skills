#!/usr/bin/env python3
"""Lint a Go controller reconcile function for operator anti-patterns.

Detects common operator bugs from static patterns in Go source: blocking calls
inside reconcile, spec mutation (instead of status), missing requeue on error,
oversized reconcile functions, and missing finalizer/condition handling. Pure
regex heuristics; not a Go AST parser, but catches the recurring mistakes.
"""
import argparse
import json
import os
import re
import sys

CODE_EXTS = {".go"}


CHECKS = [
    ("time_sleep", r"\btime\.Sleep\s*\(", "FAIL", "time.Sleep inside reconcile blocks the work queue. Use ctrl.Result{RequeueAfter: ...}."),
    ("update_spec", r"r\.(?:Client\.)?Update\(\s*ctx\s*,\s*\w+\)", "WARN", "r.Client.Update on the reconciled object likely mutates spec. Use r.Status().Update for status."),
    ("missing_context_in_http", r"http\.(?:Get|Post|Do)\s*\(", "WARN", "HTTP calls without ctx-aware client; cannot cancel during shutdown."),
    ("os_exit", r"\bos\.Exit\s*\(", "FAIL", "os.Exit inside reconcile kills the controller; return an error instead."),
    ("panic_call", r"\bpanic\s*\(", "WARN", "panic inside reconcile crashes the controller; return an error so it requeues."),
    ("log_fatal", r"\blog\.Fatal", "FAIL", "log.Fatal exits the process; return an error instead."),
]


def _read(path):
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            return f.read()
    except OSError:
        return ""


def _find_reconcile_blocks(src):
    """Return list of (start_line, end_line, body) for each Reconcile func."""
    blocks = []
    sig = re.compile(r"func\s+\([^)]*\)\s+Reconcile\s*\(", re.MULTILINE)
    for m in sig.finditer(src):
        start = m.start()
        i = src.find("{", m.end())
        if i < 0:
            continue
        depth = 1
        j = i + 1
        while j < len(src) and depth > 0:
            c = src[j]
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
            j += 1
        if depth == 0:
            body = src[i:j]
            start_line = src[:start].count("\n") + 1
            end_line = src[:j].count("\n") + 1
            blocks.append((start_line, end_line, body))
    return blocks


def _check_block(body, start_line):
    findings = []
    for key, pattern, level, msg in CHECKS:
        for m in re.finditer(pattern, body):
            line_offset = body[: m.start()].count("\n")
            findings.append({
                "level": level,
                "key": key,
                "line": start_line + line_offset,
                "msg": msg,
            })
    body_lines = body.count("\n")
    if body_lines > 80:
        findings.append({
            "level": "WARN",
            "key": "reconcile_length",
            "line": start_line,
            "msg": f"Reconcile body is {body_lines} lines (>80). Extract reconcileXxx subroutines.",
        })
    has_finalizer_add = re.search(r"controllerutil\.AddFinalizer\b|finalizers\s*=", body)
    has_finalizer_remove = re.search(r"controllerutil\.RemoveFinalizer\b", body)
    if has_finalizer_add and not has_finalizer_remove:
        findings.append({
            "level": "WARN",
            "key": "finalizer_unbalanced",
            "line": start_line,
            "msg": "AddFinalizer found but no RemoveFinalizer call — orphaned external resources on delete.",
        })
    if not re.search(r"ctrl\.Result\{", body):
        findings.append({
            "level": "WARN",
            "key": "missing_requeue",
            "line": start_line,
            "msg": "Reconcile body does not return ctrl.Result{...}. Confirm error returns trigger requeue.",
        })
    return findings


def audit_file(path):
    src = _read(path)
    if not src or "Reconcile" not in src:
        return []
    blocks = _find_reconcile_blocks(src)
    out = []
    for start_line, _, body in blocks:
        out.extend(_check_block(body, start_line))
    # Cross-function check: AddFinalizer present in file → RemoveFinalizer must be too.
    has_add = "controllerutil.AddFinalizer" in src or re.search(r"finalizers\s*=", src)
    has_remove = "controllerutil.RemoveFinalizer" in src
    if has_add and not has_remove:
        out = [f for f in out if f["key"] != "finalizer_unbalanced"]
        out.append({
            "level": "WARN",
            "key": "finalizer_unbalanced",
            "line": 0,
            "msg": "AddFinalizer is called somewhere in this file but RemoveFinalizer is not — orphaned external resources on delete.",
        })
    elif has_remove:
        # Suppress per-block warnings if file-level pairing is balanced.
        out = [f for f in out if f["key"] != "finalizer_unbalanced"]
    return out


def _walk(target):
    if os.path.isfile(target):
        yield target
        return
    for r, _, files in os.walk(target):
        for f in files:
            if os.path.splitext(f)[1] in CODE_EXTS:
                yield os.path.join(r, f)


def audit(target):
    results = []
    for path in _walk(target):
        findings = audit_file(path)
        if findings:
            results.append({"path": path, "findings": findings})
    return results


def render_text(results):
    fails = sum(1 for r in results for f in r["findings"] if f["level"] == "FAIL")
    warns = sum(1 for r in results for f in r["findings"] if f["level"] == "WARN")
    print(f"Reconcile Lint — {len(results)} controller file(s), {fails} FAIL, {warns} WARN")
    print("")
    if not results:
        print("PASS: no anti-patterns detected.")
        return 0
    for r in results:
        print(f"== {r['path']}")
        for f in r["findings"]:
            print(f"   [{f['level']}] line {f['line']}  {f['key']}: {f['msg']}")
        print("")
    return 1 if fails else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--controller", required=True, help="Path to a Go controller file or directory")
    ap.add_argument("--format", choices=["text", "json"], default="text")
    args = ap.parse_args()

    if not os.path.exists(args.controller):
        print(f"ERROR: not found: {args.controller}", file=sys.stderr)
        return 2
    results = audit(args.controller)
    if args.format == "json":
        print(json.dumps(results, indent=2))
        return 0
    return render_text(results)


if __name__ == "__main__":
    sys.exit(main())
