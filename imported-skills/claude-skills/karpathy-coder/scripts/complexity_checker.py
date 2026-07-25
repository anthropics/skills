#!/usr/bin/env python3
"""
complexity_checker.py — Detect over-engineering in Python/TypeScript files.

Karpathy Principle #2 (Simplicity First): "No abstractions for single-use code.
If you write 200 lines and it could be 50, rewrite it."

Checks:
  - Cyclomatic complexity (branches per function)
  - Class count relative to file size (too many classes = premature abstraction)
  - Nesting depth (deep nesting = hard to read)
  - Function length (long functions = doing too much)
  - Import count (many imports = over-coupled)
  - Abstract base classes / protocols for small files (premature patterns)

Usage:
    python complexity_checker.py path/to/file.py
    python complexity_checker.py src/ --threshold medium
    python complexity_checker.py . --ext py,ts --json

Thresholds:
    strict  — flags aggressively (good for new code)
    medium  — balanced (default)
    relaxed — flags only egregious cases (good for legacy code)
"""
from __future__ import annotations
import argparse
import json
import os
import re
import sys
from pathlib import Path

# --- Thresholds ---

THRESHOLDS = {
    "strict": {
        "max_cyclomatic": 5,
        "max_nesting": 3,
        "max_function_lines": 30,
        "max_imports": 10,
        "max_classes_per_100_lines": 2,
        "max_file_lines": 300,
    },
    "medium": {
        "max_cyclomatic": 8,
        "max_nesting": 4,
        "max_function_lines": 50,
        "max_imports": 15,
        "max_classes_per_100_lines": 3,
        "max_file_lines": 500,
    },
    "relaxed": {
        "max_cyclomatic": 12,
        "max_nesting": 5,
        "max_function_lines": 80,
        "max_imports": 25,
        "max_classes_per_100_lines": 5,
        "max_file_lines": 1000,
    },
}

# --- Analysis functions ---

BRANCH_KEYWORDS_PY = re.compile(
    r"^\s*(if |elif |for |while |except |with |and |or |case )", re.MULTILINE
)
BRANCH_KEYWORDS_TS = re.compile(
    r"^\s*(if\s*\(|else if|for\s*\(|while\s*\(|catch\s*\(|case |switch\s*\(|\?\?|&&|\|\|)",
    re.MULTILINE,
)
FUNC_DEF_PY = re.compile(r"^\s*(?:async\s+)?def\s+(\w+)", re.MULTILINE)
FUNC_DEF_TS = re.compile(
    r"^\s*(?:export\s+)?(?:async\s+)?(?:function\s+(\w+)|(?:const|let)\s+(\w+)\s*=\s*(?:async\s+)?\()",
    re.MULTILINE,
)
CLASS_DEF_PY = re.compile(r"^\s*class\s+\w+", re.MULTILINE)
CLASS_DEF_TS = re.compile(r"^\s*(?:export\s+)?(?:abstract\s+)?class\s+\w+", re.MULTILINE)
IMPORT_PY = re.compile(r"^(?:import |from \S+ import )", re.MULTILINE)
IMPORT_TS = re.compile(r"^import\s+", re.MULTILINE)
ABC_PATTERN = re.compile(r"ABC|abstractmethod|Protocol|@abstract|Abstract\w+Base", re.MULTILINE)
INDENT_RE = re.compile(r"^( *)\S", re.MULTILINE)


def detect_lang(path):
    ext = path.suffix.lower()
    if ext in {".py"}:
        return "python"
    if ext in {".ts", ".tsx", ".js", ".jsx"}:
        return "typescript"
    return None


def count_branches(text, lang):
    pat = BRANCH_KEYWORDS_PY if lang == "python" else BRANCH_KEYWORDS_TS
    return len(pat.findall(text))


def extract_functions(text, lang):
    """Return list of (name, start_line, line_count)."""
    pat = FUNC_DEF_PY if lang == "python" else FUNC_DEF_TS
    lines = text.splitlines()
    funcs = []
    for m in pat.finditer(text):
        name = m.group(1) or (m.group(2) if m.lastindex and m.lastindex >= 2 else "anonymous")
        start = text[:m.start()].count("\n")
        # Estimate function length: count indented lines until next same-level def or end
        indent = len(m.group(0)) - len(m.group(0).lstrip())
        end = start + 1
        for i in range(start + 1, len(lines)):
            stripped = lines[i].rstrip()
            if not stripped:
                continue
            line_indent = len(stripped) - len(stripped.lstrip())
            if line_indent <= indent and stripped.lstrip() and not stripped.lstrip().startswith(("#", "//", "/*", "*")):
                if lang == "python" and (stripped.lstrip().startswith("def ") or stripped.lstrip().startswith("class ") or stripped.lstrip().startswith("async def ")):
                    break
                if lang == "typescript" and pat.match(stripped):
                    break
            end = i + 1
        funcs.append({"name": name, "start_line": start + 1, "lines": end - start})
    return funcs


def max_nesting(text, lang):
    """Return the maximum indentation depth in the file."""
    if lang == "python":
        unit = 4
    else:
        unit = 2
    depths = []
    for m in INDENT_RE.finditer(text):
        spaces = len(m.group(1))
        depths.append(spaces // unit if unit else 0)
    return max(depths) if depths else 0


def analyze_file(path, thresholds):
    """Analyze a single file. Return dict with findings."""
    text = path.read_text(encoding="utf-8", errors="replace")
    lang = detect_lang(path)
    if not lang:
        return None

    lines = text.splitlines()
    line_count = len(lines)
    findings = []

    # File length
    if line_count > thresholds["max_file_lines"]:
        findings.append({
            "rule": "file-length",
            "severity": "warn",
            "message": f"File is {line_count} lines (max {thresholds['max_file_lines']}). Consider splitting.",
        })

    # Import count
    imp_pat = IMPORT_PY if lang == "python" else IMPORT_TS
    import_count = len(imp_pat.findall(text))
    if import_count > thresholds["max_imports"]:
        findings.append({
            "rule": "import-count",
            "severity": "warn",
            "message": f"{import_count} imports (max {thresholds['max_imports']}). High coupling?",
        })

    # Class density
    cls_pat = CLASS_DEF_PY if lang == "python" else CLASS_DEF_TS
    class_count = len(cls_pat.findall(text))
    if line_count > 0:
        density = class_count / (line_count / 100)
        if density > thresholds["max_classes_per_100_lines"]:
            findings.append({
                "rule": "class-density",
                "severity": "warn",
                "message": f"{class_count} classes in {line_count} lines ({density:.1f} per 100). Premature abstraction?",
            })

    # Premature ABC/Protocol in small files
    if class_count > 0 and line_count < 200 and ABC_PATTERN.search(text):
        findings.append({
            "rule": "premature-abstraction",
            "severity": "warn",
            "message": "Abstract base class / Protocol in a file under 200 lines. Is this needed yet?",
        })

    # Nesting depth
    depth = max_nesting(text, lang)
    if depth > thresholds["max_nesting"]:
        findings.append({
            "rule": "nesting-depth",
            "severity": "warn",
            "message": f"Max nesting depth {depth} (max {thresholds['max_nesting']}). Extract or flatten.",
        })

    # Cyclomatic complexity (file-level)
    branches = count_branches(text, lang)
    funcs = extract_functions(text, lang)
    func_count = max(len(funcs), 1)
    avg_cyclomatic = branches / func_count
    if avg_cyclomatic > thresholds["max_cyclomatic"]:
        findings.append({
            "rule": "cyclomatic-complexity",
            "severity": "warn",
            "message": f"Average cyclomatic complexity {avg_cyclomatic:.1f} (max {thresholds['max_cyclomatic']}). Simplify branching.",
        })

    # Function length
    for f in funcs:
        if f["lines"] > thresholds["max_function_lines"]:
            findings.append({
                "rule": "function-length",
                "severity": "warn",
                "message": f"Function '{f['name']}' is {f['lines']} lines (max {thresholds['max_function_lines']}). Split it.",
                "line": f["start_line"],
            })

    score = max(0, 100 - len(findings) * 15)
    return {
        "file": str(path),
        "language": lang,
        "lines": line_count,
        "functions": len(funcs),
        "classes": class_count,
        "imports": import_count,
        "max_nesting": depth,
        "avg_cyclomatic": round(avg_cyclomatic, 1),
        "score": score,
        "findings": findings,
    }


def collect_files(target, extensions):
    target = Path(target)
    if target.is_file():
        return [target]
    files = []
    for ext in extensions:
        files.extend(target.rglob(f"*.{ext}"))
    # Exclude common non-source dirs
    skip = {"node_modules", ".git", "__pycache__", ".venv", "venv", "dist", "build"}
    return [f for f in files if not any(p in skip for p in f.parts)]


def main():
    p = argparse.ArgumentParser(
        description="Detect over-engineering in Python/TypeScript files (Karpathy Principle #2).",
        epilog="Thresholds: strict (new code), medium (default), relaxed (legacy).",
    )
    p.add_argument("target", help="File or directory to analyze")
    p.add_argument(
        "--threshold",
        choices=sorted(THRESHOLDS.keys()),
        default="medium",
        help="Strictness level (default: medium)",
    )
    p.add_argument(
        "--ext",
        default="py,ts,tsx,js,jsx",
        help="Comma-separated file extensions to scan (default: py,ts,tsx,js,jsx)",
    )
    p.add_argument("--json", action="store_true", help="JSON output")
    args = p.parse_args()

    thresholds = THRESHOLDS[args.threshold]
    extensions = [e.strip().lstrip(".") for e in args.ext.split(",")]
    files = collect_files(args.target, extensions)

    if not files:
        msg = f"No files found matching extensions: {extensions}"
        if args.json:
            print(json.dumps({"status": "error", "message": msg}))
        else:
            print(f"[error] {msg}", file=sys.stderr)
        sys.exit(1)

    results = []
    for f in sorted(files):
        r = analyze_file(f, thresholds)
        if r:
            results.append(r)

    total_findings = sum(len(r["findings"]) for r in results)
    avg_score = sum(r["score"] for r in results) / len(results) if results else 100

    summary = {
        "status": "ok",
        "threshold": args.threshold,
        "files_analyzed": len(results),
        "total_findings": total_findings,
        "average_score": round(avg_score, 1),
        "verdict": "PASS" if total_findings == 0 else ("WARN" if avg_score >= 50 else "FAIL"),
        "results": results,
    }

    if args.json:
        print(json.dumps(summary, indent=2))
        return

    print(f"Karpathy Simplicity Check — {len(results)} files, threshold: {args.threshold}")
    print(f"Average score: {avg_score:.0f}/100  Findings: {total_findings}")
    print()
    for r in results:
        if not r["findings"]:
            continue
        print(f"  {r['file']}  (score {r['score']}/100)")
        for f in r["findings"]:
            line = f"  line {f['line']}" if "line" in f else ""
            print(f"    [{f['severity'].upper()}] {f['rule']}{line}: {f['message']}")
        print()
    if total_findings == 0:
        print("  No findings. Code looks appropriately simple.")
    print(f"\nVerdict: {summary['verdict']}")


if __name__ == "__main__":
    main()
