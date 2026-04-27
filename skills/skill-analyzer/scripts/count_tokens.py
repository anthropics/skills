#!/usr/bin/env python3
"""
Analyze token consumption by progressive disclosure level for a Claude Code skill.

Usage:
    python count_tokens.py <skill-path>

Levels:
    L1 - Metadata (frontmatter): always in context
    L2 - SKILL.md body: loaded when skill triggers
    L3 - Bundled resources (references/, agents/, assets/): loaded on demand
    Scripts (scripts/): executed, not loaded into context
"""

import os
import sys
from pathlib import Path


def estimate_tokens(text: str) -> int:
    """Heuristic token estimate: average of char-based and word-based methods."""
    chars = len(text)
    words = len(text.split())
    return round((chars / 3.7 + words * 1.3) / 2)


def count_tokens_api(text: str, client) -> int:
    return client.messages.count_tokens(
        model="claude-sonnet-4-6",
        messages=[{"role": "user", "content": text}]
    ).input_tokens


def parse_skill_md(skill_path: Path):
    """Split SKILL.md into frontmatter (L1) and body (L2)."""
    skill_md = skill_path / "SKILL.md"
    if not skill_md.exists():
        print(f"Error: No SKILL.md found at {skill_md}", file=sys.stderr)
        sys.exit(1)

    content = skill_md.read_text()
    lines = content.split("\n")

    # Find second --- to delimit frontmatter
    try:
        first = lines.index("---", 0)
        second = lines.index("---", first + 1)
        frontmatter = "\n".join(lines[first:second + 1])
        body = "\n".join(lines[second + 1:])
    except ValueError:
        # No frontmatter found, treat entire file as body
        frontmatter = ""
        body = content

    return frontmatter, body, content


def inventory_l3_files(skill_path: Path):
    """Collect all bundled resource files by category."""
    l3_dirs = ["references", "agents", "assets"]
    script_dir = skill_path / "scripts"

    resources = []
    scripts = []

    for d in l3_dirs:
        dir_path = skill_path / d
        if dir_path.exists():
            for f in sorted(dir_path.rglob("*")):
                if f.is_file():
                    resources.append(f)

    if script_dir.exists():
        for f in sorted(script_dir.rglob("*.py")):
            if f.is_file():
                scripts.append(f)

    return resources, scripts


def format_row(label: str, tokens, width: int = 50) -> str:
    if tokens == "—":
        return f"  {label:<{width}}   {'—':>7}  [executed, not loaded]"
    return f"  {label:<{width}}  ~{tokens:>6} tokens"


def run(skill_path_str: str):
    skill_path = Path(skill_path_str).expanduser().resolve()
    if not skill_path.exists():
        print(f"Error: skill path not found: {skill_path}", file=sys.stderr)
        sys.exit(1)

    skill_name = skill_path.name

    # Try to use the Claude API
    count_fn = None
    method_label = "Heuristic estimate (±15%)"
    api_client = None

    api_key = os.environ.get("ANTHROPIC_API_KEY")
    if api_key:
        try:
            import anthropic
            api_client = anthropic.Anthropic(api_key=api_key)
            # Quick test
            api_client.messages.count_tokens(
                model="claude-sonnet-4-6",
                messages=[{"role": "user", "content": "test"}]
            )
            count_fn = lambda t: count_tokens_api(t, api_client)
            method_label = "Claude API (exact)"
        except Exception:
            count_fn = estimate_tokens
    else:
        count_fn = estimate_tokens

    # Parse SKILL.md
    frontmatter, body, full_skill_md = parse_skill_md(skill_path)
    skill_md_lines = len((skill_path / "SKILL.md").read_text().splitlines())

    # Count L1 and L2
    t_l1 = count_fn(frontmatter) if frontmatter else 0
    t_full = count_fn(full_skill_md)
    t_l2 = t_full - t_l1

    # Inventory L3
    resources, scripts = inventory_l3_files(skill_path)
    l3_counts = []
    for f in resources:
        text = f.read_text(errors="replace")
        t = count_fn(text)
        label = str(f.relative_to(skill_path))
        l3_counts.append((label, t))

    t_l3_total = sum(t for _, t in l3_counts)

    # Print report
    sep = "─" * 62
    print(f"\n=== {skill_name}: token consumption by access level ===")
    print(f"Method: {method_label}\n")

    print("LEVEL 1 — Metadata (always in context)")
    print(format_row("SKILL.md frontmatter", t_l1))
    print()

    print("LEVEL 2 — SKILL.md body (loaded when skill triggers)")
    print(format_row("SKILL.md body", t_l2))
    print(f"  {sep}")
    print(format_row("Full SKILL.md (L1 + L2)", t_full))
    print()

    if l3_counts or scripts:
        print("LEVEL 3 — Bundled resources (loaded on demand)")
        for label, t in l3_counts:
            print(format_row(label, t))
        for f in scripts:
            label = str(f.relative_to(skill_path))
            print(format_row(label, "—"))
        if l3_counts:
            print(f"  {sep}")
            print(format_row("All L3 combined", t_l3_total))
        print()

    print("=== Cumulative by scenario ===")
    print(format_row("Not triggered (L1 metadata only)", t_l1))
    print(format_row("Triggered, no L3 loaded (L1 + L2)", t_full))
    if l3_counts:
        print(format_row("All resources loaded (L1 + L2 + all L3)", t_full + t_l3_total))

    # Observations
    notes = []
    if skill_md_lines >= 450:
        notes.append(f"SKILL.md is {skill_md_lines} lines — approaching the 500-line recommended limit.")
    elif skill_md_lines >= 350:
        notes.append(f"SKILL.md is {skill_md_lines} lines — still within limits but worth watching.")

    large_l3 = [(label, t) for label, t in l3_counts if t > 1500]
    for label, t in large_l3:
        notes.append(f"{label} is large (~{t} tokens) — consider adding a table of contents if >300 lines.")

    if scripts:
        script_names = ", ".join(str(f.relative_to(skill_path)) for f in scripts)
        notes.append(f"Scripts ({script_names}) are executed, not loaded — they add no context cost unless explicitly Read.")

    if not api_key:
        notes.append("Set ANTHROPIC_API_KEY for exact token counts via the Claude API.")

    if notes:
        print("\n--- Observations ---")
        for note in notes:
            print(f"  • {note}")

    print()


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <skill-path>", file=sys.stderr)
        sys.exit(1)
    run(sys.argv[1])
