#!/usr/bin/env python3
"""Build a domain harness manifest: scan a domain folder's skills and emit the
machine-readable inventory (skills, tools, verification checks, agentic signals)
that goal_compiler.py and loop_controller.py consume.

Stdlib-only. Deterministic: same tree in, same manifest out (modulo the
generated_at stamp, which --no-timestamp suppresses for diff-stable output).

Usage:
  python3 harness_manifest_builder.py --domain engineering --repo-root . --json
  python3 harness_manifest_builder.py --all --repo-root . --out-dir assets/harnesses --no-timestamp
  python3 harness_manifest_builder.py --sample
"""

import argparse
import datetime
import json
import os
import re
import sys

SCHEMA = "agent-harness/manifest.v1"

# Folders that are never skill content.
SKIP_DIRS = {".git", ".github", "node_modules", "__pycache__", ".claude-plugin",
             "expected_outputs", ".codex", ".gemini", ".hermes", ".vibe"}

# Signal regexes: cheap, static evidence that a skill already carries agentic
# structure. Matched case-insensitively against the SKILL.md body.
SIGNALS = {
    "goal_intake": r"forcing[- ]question|before starting|intake|clarify(?:ing)? question",
    "refusal_gate": r"refus(?:e|al)|exit(?:s|ed)? (?:code )?[1-9]|hard rule|NO-GO",
    "verification": r"verif(?:y|ication|iable)|checklist|--sample|exit 0|definition of done",
    "loop_discipline": r"\bretry\b|\biterat(?:e|ion)|stop condition|max attempts|budget|until",
    "close_out": r"close[- ]?(?:the[- ])?loop|handoff|hand-off|state persist|done when|completion",
}

LOOP_DEFAULTS = {
    "max_attempts_per_task": 3,
    "max_loop_iterations": 12,
    "escalate_on": [
        "attempts_exhausted",
        "no_verification_available",
        "destructive_or_irreversible_action",
        "goal_drift_detected",
    ],
}


def read_text(path):
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            return f.read()
    except OSError:
        return ""


def truncate_words(text, limit):
    """Cap at `limit` chars, cutting on a word boundary with an ellipsis marker."""
    if len(text) <= limit:
        return text
    cut = text[:limit - 2]
    if " " in cut:
        cut = cut.rsplit(" ", 1)[0]
    return cut.rstrip(",;:") + " …"


def parse_frontmatter(text):
    """Extract name/description from YAML frontmatter without a YAML dep."""
    meta = {"name": "", "description": ""}
    if not text.startswith("---"):
        return meta
    end = text.find("\n---", 3)
    if end == -1:
        return meta
    block = text[3:end]
    m = re.search(r"^name:\s*(.+)$", block, re.MULTILINE)
    if m:
        meta["name"] = m.group(1).strip().strip("\"'")
    m = re.search(r"^description:\s*(.+)$", block, re.MULTILINE)
    if m:
        desc = m.group(1).strip()
        # Fold simple multi-line continuations (indented lines).
        idx = block.find(m.group(0)) + len(m.group(0))
        for line in block[idx:].splitlines():
            if line.startswith(("  ", "\t")) and not re.match(r"^\s*\w+:", line):
                desc += " " + line.strip()
            elif line.strip():
                break
        meta["description"] = desc.strip().strip("\"'")
    return meta


def find_skills(domain_path):
    """Yield (skill_dir, skill_md_path) for every SKILL.md under the domain."""
    hits = []
    for root, dirs, files in os.walk(domain_path):
        dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS)
        if "SKILL.md" in files:
            hits.append((root, os.path.join(root, "SKILL.md")))
    return sorted(hits)


def scan_skill(skill_dir, skill_md, repo_root):
    text = read_text(skill_md)
    meta = parse_frontmatter(text)
    body = text.lower()
    rel_dir = os.path.relpath(skill_dir, repo_root)

    tools = []
    scripts_dir = os.path.join(skill_dir, "scripts")
    script_paths = []
    if os.path.isdir(scripts_dir):
        for fn in sorted(os.listdir(scripts_dir)):
            if fn.endswith(".py"):
                script_paths.append(os.path.join(scripts_dir, fn))
    # Root-level scripts (older layout).
    for fn in sorted(os.listdir(skill_dir)):
        if fn.endswith(".py"):
            script_paths.append(os.path.join(skill_dir, fn))

    for sp in script_paths:
        rel = os.path.relpath(sp, repo_root)
        src = read_text(sp)
        tools.append({
            "script": rel,
            "wired": os.path.basename(sp) in text,
            "supports_sample": "--sample" in src,
            "verification": build_checks(rel, src),
        })

    signals = {k: bool(re.search(rx, body)) for k, rx in SIGNALS.items()}
    return {
        "name": meta["name"] or os.path.basename(skill_dir),
        "path": rel_dir,
        "description": truncate_words(meta["description"], 600),
        "tools": tools,
        "agentic_signals": signals,
        "references": sorted(os.listdir(os.path.join(skill_dir, "references")))
        if os.path.isdir(os.path.join(skill_dir, "references")) else [],
    }


def build_checks(rel_script, src):
    checks = [{"cmd": "python3 %s --help" % rel_script, "expect_exit": 0,
               "kind": "smoke"}]
    if "--sample" in src:
        checks.append({"cmd": "python3 %s --sample" % rel_script,
                       "expect_exit": 0, "kind": "sample"})
    return checks


def build_manifest(domain_path, repo_root, timestamp=True):
    domain = os.path.relpath(domain_path, repo_root)
    skills = [scan_skill(d, s, repo_root) for d, s in find_skills(domain_path)]
    manifest = {
        "schema": SCHEMA,
        "domain": domain,
        "skill_count": len(skills),
        "loop_defaults": LOOP_DEFAULTS,
        "skills": skills,
    }
    if timestamp:
        manifest["generated_at"] = (
            datetime.datetime.now(datetime.timezone.utc)
            .strftime("%Y-%m-%dT%H:%M:%SZ"))
    return manifest


SAMPLE_MANIFEST = {
    "schema": SCHEMA,
    "domain": "engineering",
    "skill_count": 1,
    "loop_defaults": LOOP_DEFAULTS,
    "skills": [{
        "name": "slo-architect",
        "path": "engineering/slo-architect/skills/slo-architect",
        "description": "Design SLOs/SLIs and error budgets per the Google SRE Workbook...",
        "tools": [{
            "script": "engineering/slo-architect/skills/slo-architect/scripts/error_budget_calculator.py",
            "wired": True,
            "supports_sample": True,
            "verification": [
                {"cmd": "python3 .../error_budget_calculator.py --help",
                 "expect_exit": 0, "kind": "smoke"},
                {"cmd": "python3 .../error_budget_calculator.py --sample",
                 "expect_exit": 0, "kind": "sample"},
            ],
        }],
        "agentic_signals": {
            "goal_intake": True, "refusal_gate": True, "verification": True,
            "loop_discipline": True, "close_out": True,
        },
        "references": ["slo_canon.md"],
    }],
}


def main():
    ap = argparse.ArgumentParser(
        description="Scan a domain folder and emit its agent-harness manifest.")
    ap.add_argument("--domain", action="append", default=[],
                    help="Domain folder relative to --repo-root (repeatable).")
    ap.add_argument("--all", action="store_true",
                    help="Build manifests for every top-level domain folder "
                         "containing at least one SKILL.md.")
    ap.add_argument("--repo-root", default=".")
    ap.add_argument("--out-dir", help="Write <domain>.json per domain here.")
    ap.add_argument("--json", action="store_true",
                    help="Print manifest(s) to stdout as JSON.")
    ap.add_argument("--no-timestamp", action="store_true",
                    help="Omit generated_at for diff-stable committed manifests.")
    ap.add_argument("--sample", action="store_true",
                    help="Print an example manifest and exit 0.")
    args = ap.parse_args()

    if args.sample:
        print(json.dumps(SAMPLE_MANIFEST, indent=2))
        return 0

    repo_root = os.path.abspath(args.repo_root)
    targets = list(args.domain)
    if args.all:
        for entry in sorted(os.listdir(repo_root)):
            p = os.path.join(repo_root, entry)
            if (os.path.isdir(p) and entry not in SKIP_DIRS
                    and not entry.startswith(".")
                    and find_skills(p)):
                targets.append(entry)
    if not targets:
        ap.error("provide --domain, --all, or --sample")

    results = []
    for t in sorted(set(targets)):
        dp = os.path.join(repo_root, t)
        if not os.path.isdir(dp):
            print("ERROR: no such domain folder: %s" % t, file=sys.stderr)
            return 2
        manifest = build_manifest(dp, repo_root, timestamp=not args.no_timestamp)
        results.append(manifest)
        if args.out_dir:
            os.makedirs(args.out_dir, exist_ok=True)
            slug = t.rstrip("/").replace(os.sep, "-")
            out = os.path.join(args.out_dir, "%s.json" % slug)
            with open(out, "w", encoding="utf-8") as f:
                json.dump(manifest, f, indent=2, sort_keys=False)
                f.write("\n")
            print("wrote %s (%d skills)" % (out, manifest["skill_count"]),
                  file=sys.stderr)

    if args.json or not args.out_dir:
        print(json.dumps(results if len(results) > 1 else results[0], indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
