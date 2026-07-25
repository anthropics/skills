#!/usr/bin/env python3
"""okf_linter.py — Validates the OKF (Open Knowledge Format) conformance of a company bundle.

Rules checked (see references/okf_conformance.md):
  1. Every concept (.md that is not index.md/log.md) has frontmatter with a non-empty `type`.   [ERROR]
  2. The `type` belongs to the controlled vocabulary.                                            [WARNING]
  3. index.md / log.md do NOT have a `type`.                                                      [ERROR]
  4. Relative markdown links (.md) resolve to existing files.                                     [ERROR]
  5. Every folder with concepts has an index.md.                                                  [WARNING]

Exits with code 0 if there are no ERRORS (warnings do not fail). Deterministic, standard library only.

Usage:
    python okf_linter.py                       # lint an embedded example bundle (PASS)
    python okf_linter.py ./my-company
    python okf_linter.py ./my-company --output json
    python okf_linter.py --sample              # same as the first
"""

import argparse
import json
import os
import re
import sys
import tempfile

VALID_TYPES = {
    "Foundation", "Problem-Solution", "Strategy", "Market Analysis", "Persona",
    "Financial Model", "Sales Process", "Playbook", "Brand",
    "Content Strategy", "Product Document", "Process", "Runbook",
    "Operational Resource", "Architecture", "Organization", "Legal Document",
    "OKR", "Metric", "Ritual",
}

RESERVED = {"index.md", "log.md"}
LINK_RE = re.compile(r"\[[^\]]+\]\(([^)]+\.md)(?:#[^)]*)?\)")


def parse_frontmatter(text):
    """Returns (has_frontmatter, simple_dict). Minimal parser: top-level key: value pairs."""
    if not text.startswith("---"):
        return False, {}
    end = text.find("\n---", 3)
    if end == -1:
        return False, {}
    block = text[3:end].strip("\n")
    fm = {}
    for line in block.splitlines():
        if line and not line.startswith((" ", "\t")) and ":" in line:
            key, _, val = line.partition(":")
            fm[key.strip()] = val.strip().strip('"').strip("'")
    return True, fm


def lint(bundle_dir):
    findings = []  # each item: {severity, rule, path, detail}
    bundle_dir = os.path.abspath(bundle_dir)

    md_files = []
    dirs_with_concepts = set()
    for root, _, files in os.walk(bundle_dir):
        for name in files:
            if name.endswith(".md"):
                full = os.path.join(root, name)
                md_files.append(full)
                if name not in RESERVED:
                    dirs_with_concepts.add(root)

    for full in sorted(md_files):
        rel = os.path.relpath(full, bundle_dir)
        name = os.path.basename(full)
        try:
            with open(full, "r", encoding="utf-8") as f:
                text = f.read()
        except (IOError, OSError) as e:
            findings.append({"severity": "error", "rule": "read", "path": rel, "detail": str(e)})
            continue

        has_fm, fm = parse_frontmatter(text)
        is_reserved = name in RESERVED

        if is_reserved:
            if has_fm and fm.get("type"):
                findings.append({"severity": "error", "rule": "reserved_without_type", "path": rel,
                                 "detail": f"{name} is reserved and cannot have a `type`"})
        else:
            tp = fm.get("type", "").strip() if has_fm else ""
            if not tp:
                findings.append({"severity": "error", "rule": "type_required", "path": rel,
                                 "detail": "concept without `type` in frontmatter"})
            elif tp not in VALID_TYPES:
                findings.append({"severity": "warning", "rule": "type_unknown", "path": rel,
                                 "detail": f"`type: {tp}` outside the vocabulary"})

        # relative .md links resolve
        for m in LINK_RE.finditer(text):
            target = m.group(1)
            if target.startswith("http"):
                continue
            resolved = os.path.normpath(os.path.join(os.path.dirname(full), target))
            if not os.path.exists(resolved):
                findings.append({"severity": "error", "rule": "broken_link", "path": rel,
                                 "detail": f"link to nonexistent file: {target}"})

    # folders with concepts have an index.md
    for d in sorted(dirs_with_concepts):
        if not os.path.exists(os.path.join(d, "index.md")):
            rel = os.path.relpath(d, bundle_dir) or "."
            findings.append({"severity": "warning", "rule": "index_missing", "path": rel,
                             "detail": "folder with concepts without an index.md"})

    errors = [f for f in findings if f["severity"] == "error"]
    warnings = [f for f in findings if f["severity"] == "warning"]
    return {
        "bundle": bundle_dir,
        "md_files": len(md_files),
        "errors": len(errors),
        "warnings": len(warnings),
        "findings": findings,
        "verdict": "PASS" if not errors else "FAIL",
    }


def build_sample_bundle(base):
    """Creates a minimal and CONFORMANT bundle for demonstration; returns the path."""
    root = os.path.join(base, "exemplo")
    os.makedirs(os.path.join(root, "00-fundacao"), exist_ok=True)
    with open(os.path.join(root, "index.md"), "w", encoding="utf-8") as f:
        f.write("# Example\n\n[Foundation](00-fundacao/index.md)\n")
    with open(os.path.join(root, "log.md"), "w", encoding="utf-8") as f:
        f.write("# Log\n\n## 2026-01-01T00:00:00Z — created\n")
    with open(os.path.join(root, "00-fundacao", "index.md"), "w", encoding="utf-8") as f:
        f.write("# Foundation\n\n[identidade](identidade.md)\n")
    with open(os.path.join(root, "00-fundacao", "identidade.md"), "w", encoding="utf-8") as f:
        f.write("---\ntype: Foundation\ntitle: Identity\n---\n\n# Identity\n\nBack to [index](index.md).\n")
    return root


def render_text(r):
    out = []
    out.append("=" * 64)
    out.append("OKF LINTER")
    out.append(f"Bundle: {r['bundle']}")
    out.append(f".md files: {r['md_files']}   Errors: {r['errors']}   Warnings: {r['warnings']}")
    out.append("=" * 64)
    if not r["findings"]:
        out.append("  No problems found.")
    for f in r["findings"]:
        tag = "ERROR" if f["severity"] == "error" else "WARN "
        out.append(f"  [{tag}] {f['rule']:22s} {f['path']}: {f['detail']}")
    out.append("-" * 64)
    out.append(f"Verdict: {r['verdict']}")
    return "\n".join(out)


def main():
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass

    p = argparse.ArgumentParser(
        description="Validates the OKF conformance of a company bundle.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    p.add_argument("path", nargs="?", help="Bundle folder (omitted = embedded example bundle)")
    p.add_argument("--sample", action="store_true", help="Uses the embedded example bundle")
    p.add_argument("--output", choices=("text", "json"), default="text")
    args = p.parse_args()

    if args.path and not args.sample:
        if not os.path.isdir(args.path):
            print(f"error: not a folder: {args.path}", file=sys.stderr)
            return 2
        result = lint(args.path)
    else:
        with tempfile.TemporaryDirectory() as tmp:
            result = lint(build_sample_bundle(tmp))
            result["bundle"] = "<embedded example bundle>"

    if args.output == "json":
        print(json.dumps(result, indent=2, ensure_ascii=False))
    else:
        print(render_text(result))
    return 0 if result["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
