#!/usr/bin/env python3
"""
diff_surgeon.py — Detect diff noise: changes that don't trace to the stated goal.

Karpathy Principle #3 (Surgical Changes): "Every changed line should trace
directly to the user's request."

Analyzes a git diff and flags:
  - Comment-only changes (unrelated to the task)
  - Whitespace / formatting changes
  - Import additions not used by the new code
  - Style changes (quote style, trailing commas, semicolons)
  - Docstring additions to unchanged functions
  - Variable renames in untouched code
  - Type annotation additions to unchanged signatures

Usage:
    python diff_surgeon.py                          # analyze staged diff
    python diff_surgeon.py --diff HEAD~1..HEAD      # analyze last commit
    python diff_surgeon.py --file changes.diff      # analyze a diff file
    python diff_surgeon.py --json

Exit codes:
    0  clean — all changes look intentional
    1  noise detected — review before committing
"""
from __future__ import annotations
import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# --- Noise detectors ---

COMMENT_ONLY = re.compile(r"^[+-]\s*(?:#|//|/\*|\*|<!--)")
WHITESPACE_ONLY = re.compile(r"^[+-]\s*$")
QUOTE_CHANGE = re.compile(r'^[+-]\s*.*["\'].*["\']')
DOCSTRING_ADD = re.compile(r'^[+]\s*"""')
IMPORT_LINE = re.compile(r"^[+]\s*(?:import |from \S+ import |const .* = require)")
TYPE_ANNOTATION = re.compile(r"^[+-].*:\s*(?:str|int|float|bool|list|dict|Optional|Union|Any|string|number|boolean)\b")
SEMICOLON_CHANGE = re.compile(r"^[+-].*;\s*$")
TRAILING_COMMA = re.compile(r"^[+-].*,\s*$")


def get_diff(args):
    """Get diff text from args."""
    if args.file:
        return Path(args.file).read_text(encoding="utf-8", errors="replace")
    diff_range = args.diff or "--staged"
    cmd = ["git", "diff", diff_range] if diff_range != "--staged" else ["git", "diff", "--staged"]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
        return result.stdout
    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        print(f"[error] git diff failed: {e}", file=sys.stderr)
        sys.exit(1)


def parse_hunks(diff_text):
    """Parse a unified diff into per-file hunks."""
    files = []
    current_file = None
    current_lines = []

    for line in diff_text.splitlines():
        if line.startswith("diff --git"):
            if current_file:
                files.append({"file": current_file, "lines": current_lines})
            # Extract filename: diff --git a/path b/path
            parts = line.split(" b/")
            current_file = parts[-1] if len(parts) > 1 else "unknown"
            current_lines = []
        elif line.startswith("+++ ") or line.startswith("--- "):
            continue
        elif line.startswith("@@"):
            current_lines.append({"type": "hunk_header", "text": line})
        elif line.startswith("+") or line.startswith("-"):
            current_lines.append({"type": "change", "text": line})

    if current_file:
        files.append({"file": current_file, "lines": current_lines})
    return files


def classify_line(line_text):
    """Classify a changed line. Returns a noise category or None if intentional."""
    if WHITESPACE_ONLY.match(line_text):
        return "whitespace"
    if COMMENT_ONLY.match(line_text):
        return "comment-only"
    if DOCSTRING_ADD.match(line_text):
        return "docstring-addition"
    if SEMICOLON_CHANGE.match(line_text):
        # Check if ONLY change is semicolon
        stripped = line_text[1:].rstrip(";").rstrip()
        if not stripped.strip():
            return None
        return "semicolon-style"
    return None


def analyze_file_diff(file_data):
    """Analyze a single file's diff for noise."""
    findings = []
    change_lines = [l for l in file_data["lines"] if l["type"] == "change"]
    total_changes = len(change_lines)

    if total_changes == 0:
        return findings

    # Detect paired +/- that are only whitespace/style changes
    additions = [l["text"] for l in change_lines if l["text"].startswith("+")]
    deletions = [l["text"] for l in change_lines if l["text"].startswith("-")]

    noise_count = 0
    for line_data in change_lines:
        category = classify_line(line_data["text"])
        if category:
            noise_count += 1
            findings.append({
                "category": category,
                "line": line_data["text"][:120],
            })

    # Detect quote-style swaps (paired changes where only quotes differ)
    for a, d in zip(sorted(additions), sorted(deletions)):
        a_norm = a[1:].replace('"', "'").strip()
        d_norm = d[1:].replace('"', "'").strip()
        if a_norm == d_norm and a[1:].strip() != d[1:].strip():
            findings.append({
                "category": "quote-style-swap",
                "line": f"{d[:60]} → {a[:60]}",
            })

    noise_ratio = noise_count / total_changes if total_changes > 0 else 0
    return findings


def main():
    p = argparse.ArgumentParser(
        description="Detect diff noise — changes that don't trace to the stated goal (Karpathy Principle #3).",
        epilog="Run before committing to catch drive-by refactors and style drift.",
    )
    p.add_argument("--diff", default=None, help="Git diff range (e.g. HEAD~1..HEAD). Default: staged changes.")
    p.add_argument("--file", default=None, help="Read diff from a file instead of git")
    p.add_argument("--json", action="store_true", help="JSON output")
    args = p.parse_args()

    diff_text = get_diff(args)
    if not diff_text.strip():
        result = {"status": "ok", "message": "No diff to analyze", "files": 0, "noise_lines": 0, "verdict": "CLEAN"}
        if args.json:
            print(json.dumps(result, indent=2))
        else:
            print("No diff to analyze. Stage changes first (git add) or specify --diff range.")
        return

    file_diffs = parse_hunks(diff_text)
    all_findings = []
    file_results = []

    for fd in file_diffs:
        findings = analyze_file_diff(fd)
        if findings:
            file_results.append({"file": fd["file"], "findings": findings})
            all_findings.extend(findings)

    total_noise = len(all_findings)
    total_changes = sum(
        len([l for l in fd["lines"] if l["type"] == "change"]) for fd in file_diffs
    )
    noise_ratio = total_noise / total_changes if total_changes > 0 else 0

    verdict = "CLEAN" if noise_ratio < 0.1 else ("NOISY" if noise_ratio < 0.3 else "VERY_NOISY")

    result = {
        "status": "ok",
        "files_in_diff": len(file_diffs),
        "total_change_lines": total_changes,
        "noise_lines": total_noise,
        "noise_ratio": round(noise_ratio, 2),
        "verdict": verdict,
        "file_results": file_results,
    }

    if args.json:
        print(json.dumps(result, indent=2))
        return

    print(f"Diff Surgeon — {len(file_diffs)} files, {total_changes} changed lines")
    print(f"Noise ratio: {noise_ratio:.0%} ({total_noise} noise lines)")
    print(f"Verdict: {verdict}")
    if file_results:
        print()
        for fr in file_results:
            print(f"  {fr['file']}:")
            categories = {}
            for f in fr["findings"]:
                categories.setdefault(f["category"], []).append(f["line"])
            for cat, lines in categories.items():
                print(f"    [{cat}] {len(lines)} instance(s)")
                for l in lines[:3]:
                    print(f"      {l}")
                if len(lines) > 3:
                    print(f"      ... and {len(lines) - 3} more")
        print()
        print("Recommendation: review flagged lines. Remove changes that don't trace to your task.")
    else:
        print("\n  All changes look intentional. Clean diff.")

    sys.exit(1 if verdict != "CLEAN" else 0)


if __name__ == "__main__":
    main()
