#!/usr/bin/env python3
"""Dry-run validation for the AgentHub plugin.

Checks JSON validity, YAML frontmatter, markdown structure, cross-file
consistency, script --help, and referenced file existence — without
creating any sessions or worktrees.

Usage:
    python dry_run.py                # Run all checks
    python dry_run.py --verbose      # Show per-file details
    python dry_run.py --help
"""

import argparse
import json
import os
import re
import subprocess
import sys

PLUGIN_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ── Helpers ──────────────────────────────────────────────────────────

PASS = "\033[32m✓\033[0m"
FAIL = "\033[31m✗\033[0m"
WARN = "\033[33m!\033[0m"


class Results:
    def __init__(self):
        self.passed = 0
        self.failed = 0
        self.warnings = 0
        self.details = []

    def ok(self, msg):
        self.passed += 1
        self.details.append((PASS, msg))

    def fail(self, msg):
        self.failed += 1
        self.details.append((FAIL, msg))

    def warn(self, msg):
        self.warnings += 1
        self.details.append((WARN, msg))

    def print(self, verbose=False):
        if verbose:
            for icon, msg in self.details:
                print(f"  {icon} {msg}")
            print()
        total = self.passed + self.failed
        status = "PASS" if self.failed == 0 else "FAIL"
        color = "\033[32m" if self.failed == 0 else "\033[31m"
        warn_str = f", {self.warnings} warnings" if self.warnings else ""
        print(f"{color}{status}\033[0m  {self.passed}/{total} checks passed{warn_str}")
        return self.failed == 0


def rel(path):
    """Path relative to plugin root for display."""
    return os.path.relpath(path, PLUGIN_ROOT)


# ── Check 1: JSON files ─────────────────────────────────────────────

def check_json(results):
    """Validate settings.json and plugin.json."""
    json_files = [
        os.path.join(PLUGIN_ROOT, "settings.json"),
        os.path.join(PLUGIN_ROOT, ".claude-plugin", "plugin.json"),
    ]
    for path in json_files:
        name = rel(path)
        if not os.path.exists(path):
            results.fail(f"{name} — file missing")
            continue
        try:
            with open(path) as f:
                data = json.load(f)
            results.ok(f"{name} — valid JSON")
        except json.JSONDecodeError as e:
            results.fail(f"{name} — invalid JSON: {e}")
            continue

        # plugin.json: only allowed fields
        if name.endswith("plugin.json"):
            allowed = {"name", "description", "version", "author", "homepage",
                       "repository", "license", "skills"}
            extra = set(data.keys()) - allowed
            if extra:
                results.fail(f"{name} — disallowed fields: {extra}")
            else:
                results.ok(f"{name} — schema fields OK")

    # Cross-check versions
    try:
        with open(json_files[0]) as f:
            v1 = json.load(f).get("version")
        with open(json_files[1]) as f:
            v2 = json.load(f).get("version")
        if v1 and v2 and v1 == v2:
            results.ok(f"version match ({v1})")
        elif v1 and v2:
            results.fail(f"version mismatch: settings={v1}, plugin={v2}")
    except Exception:
        pass


# ── Check 2: YAML frontmatter ───────────────────────────────────────

FRONTMATTER_RE = re.compile(r"^---\n(.+?)\n---", re.DOTALL)
REQUIRED_FM_KEYS = {"name", "description"}


def check_frontmatter(results):
    """Validate YAML frontmatter in all SKILL.md files."""
    skill_files = []
    for root, _dirs, files in os.walk(PLUGIN_ROOT):
        for f in files:
            if f == "SKILL.md":
                skill_files.append(os.path.join(root, f))

    for path in skill_files:
        name = rel(path)
        with open(path) as f:
            content = f.read()
        m = FRONTMATTER_RE.match(content)
        if not m:
            results.fail(f"{name} — missing YAML frontmatter")
            continue
        # Lightweight key check (no PyYAML dependency)
        fm_text = m.group(1)
        found_keys = set()
        for line in fm_text.splitlines():
            if ":" in line:
                key = line.split(":", 1)[0].strip()
                found_keys.add(key)
        missing = REQUIRED_FM_KEYS - found_keys
        if missing:
            results.fail(f"{name} — frontmatter missing keys: {missing}")
        else:
            results.ok(f"{name} — frontmatter OK")


# ── Check 3: Markdown structure ──────────────────────────────────────

def check_markdown(results):
    """Check for broken code fences and table rows in all .md files."""
    md_files = []
    for root, _dirs, files in os.walk(PLUGIN_ROOT):
        for f in files:
            if f.endswith(".md"):
                md_files.append(os.path.join(root, f))

    for path in md_files:
        name = rel(path)
        with open(path) as f:
            lines = f.readlines()

        # Code fences must be balanced
        fence_count = sum(1 for ln in lines if ln.strip().startswith("```"))
        if fence_count % 2 != 0:
            results.fail(f"{name} — unbalanced code fences ({fence_count} found)")
        else:
            results.ok(f"{name} — code fences balanced")

        # Tables: rows inside a table should have consistent pipe count
        in_table = False
        table_pipes = 0
        table_ok = True
        for i, ln in enumerate(lines, 1):
            stripped = ln.strip()
            if stripped.startswith("|") and stripped.endswith("|"):
                pipes = stripped.count("|")
                if not in_table:
                    in_table = True
                    table_pipes = pipes
                elif pipes != table_pipes:
                    # Separator rows (|---|---| ) can differ slightly; skip
                    if not re.match(r"^\|[\s\-:|]+\|$", stripped):
                        results.warn(f"{name}:{i} — table column count mismatch ({pipes} vs {table_pipes})")
                        table_ok = False
            else:
                in_table = False
                table_pipes = 0


# ── Check 4: Scripts --help ──────────────────────────────────────────

def check_scripts(results):
    """Verify every Python script exits 0 on --help."""
    scripts_dir = os.path.join(PLUGIN_ROOT, "scripts")
    if not os.path.isdir(scripts_dir):
        results.warn("scripts/ directory not found")
        return

    for fname in sorted(os.listdir(scripts_dir)):
        if not fname.endswith(".py") or fname == "dry_run.py":
            continue
        path = os.path.join(scripts_dir, fname)
        try:
            proc = subprocess.run(
                [sys.executable, path, "--help"],
                capture_output=True, text=True, timeout=10,
            )
            if proc.returncode == 0:
                results.ok(f"scripts/{fname} --help exits 0")
            else:
                results.fail(f"scripts/{fname} --help exits {proc.returncode}")
        except subprocess.TimeoutExpired:
            results.fail(f"scripts/{fname} --help timed out")
        except Exception as e:
            results.fail(f"scripts/{fname} --help error: {e}")


# ── Check 5: Referenced files exist ──────────────────────────────────

def check_references(results):
    """Verify that key files referenced in docs actually exist."""
    expected = [
        "settings.json",
        ".claude-plugin/plugin.json",
        "CLAUDE.md",
        "SKILL.md",
        "README.md",
        "agents/hub-coordinator.md",
        "references/agent-templates.md",
        "references/coordination-strategies.md",
        "scripts/hub_init.py",
        "scripts/dag_analyzer.py",
        "scripts/board_manager.py",
        "scripts/result_ranker.py",
        "scripts/session_manager.py",
    ]
    for ref in expected:
        path = os.path.join(PLUGIN_ROOT, ref)
        if os.path.exists(path):
            results.ok(f"{ref} exists")
        else:
            results.fail(f"{ref} — referenced but missing")


# ── Check 6: Cross-domain coverage ──────────────────────────────────

def check_cross_domain(results):
    """Verify non-engineering examples exist in key files (the whole point of this update)."""
    checks = [
        ("settings.json", "content-generation"),
        (".claude-plugin/plugin.json", "content drafts"),
        ("CLAUDE.md", "content drafts"),
        ("SKILL.md", "content variation"),
        ("README.md", "content generation"),
        ("skills/run/SKILL.md", "--judge"),
        ("skills/init/SKILL.md", "LLM judge"),
        ("skills/eval/SKILL.md", "narrative"),
        ("skills/board/SKILL.md", "Storytelling"),
        ("skills/status/SKILL.md", "Storytelling"),
        ("references/agent-templates.md", "landing page copy"),
        ("references/coordination-strategies.md", "flesch_score"),
        ("agents/hub-coordinator.md", "qualitative verdict"),
    ]
    for filepath, needle in checks:
        path = os.path.join(PLUGIN_ROOT, filepath)
        if not os.path.exists(path):
            results.fail(f"{filepath} — missing (cannot check cross-domain)")
            continue
        with open(path) as f:
            content = f.read()
        if needle.lower() in content.lower():
            results.ok(f"{filepath} — contains cross-domain example (\"{needle}\")")
        else:
            results.fail(f"{filepath} — missing cross-domain marker \"{needle}\"")


# ── Main ─────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Dry-run validation for the AgentHub plugin."
    )
    parser.add_argument("--verbose", "-v", action="store_true",
                        help="Show per-file check details")
    args = parser.parse_args()

    print(f"AgentHub dry-run validation")
    print(f"Plugin root: {PLUGIN_ROOT}\n")

    all_ok = True
    sections = [
        ("JSON validity", check_json),
        ("YAML frontmatter", check_frontmatter),
        ("Markdown structure", check_markdown),
        ("Script --help", check_scripts),
        ("Referenced files", check_references),
        ("Cross-domain examples", check_cross_domain),
    ]

    for title, fn in sections:
        print(f"── {title} ──")
        r = Results()
        fn(r)
        ok = r.print(verbose=args.verbose)
        if not ok:
            all_ok = False
        print()

    if all_ok:
        print("\033[32mAll checks passed.\033[0m")
    else:
        print("\033[31mSome checks failed — see above.\033[0m")
        sys.exit(1)


if __name__ == "__main__":
    main()
