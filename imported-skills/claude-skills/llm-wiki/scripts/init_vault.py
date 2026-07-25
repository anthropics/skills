#!/usr/bin/env python3
"""
init_vault.py — Bootstrap an LLM Wiki vault.

Creates the three-layer structure (raw/, wiki/, schema files) and seeds it with
starter templates for CLAUDE.md, AGENTS.md, index.md, log.md, and page templates.

Usage:
    python init_vault.py --path ~/vaults/research --topic "LLM interpretability"
    python init_vault.py --path ./my-wiki --topic "Book: The Power Broker" --tool codex

The --tool flag controls which schema file(s) to install:
    claude-code  → CLAUDE.md (default)
    codex        → AGENTS.md
    cursor       → AGENTS.md + .cursorrules
    antigravity  → AGENTS.md
    all          → CLAUDE.md + AGENTS.md + .cursorrules (recommended for multi-tool)
"""
from __future__ import annotations
import argparse
import datetime as dt
import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
PLUGIN_DIR = SCRIPT_DIR.parent
ASSETS_DIR = PLUGIN_DIR / "assets"

VAULT_DIRS = [
    "raw",
    "raw/assets",
    "wiki",
    "wiki/entities",
    "wiki/concepts",
    "wiki/sources",
    "wiki/comparisons",
    "wiki/synthesis",
]

TOOL_FILES = {
    "claude-code": ["CLAUDE.md.template:CLAUDE.md"],
    "codex": ["AGENTS.md.template:AGENTS.md"],
    "cursor": ["AGENTS.md.template:AGENTS.md", "cursorrules.template:.cursorrules"],
    "antigravity": ["AGENTS.md.template:AGENTS.md"],
    "opencode": ["AGENTS.md.template:AGENTS.md"],
    "gemini-cli": ["AGENTS.md.template:AGENTS.md"],
    "all": [
        "CLAUDE.md.template:CLAUDE.md",
        "AGENTS.md.template:AGENTS.md",
        "cursorrules.template:.cursorrules",
    ],
}


def render_template(src, dest, variables):
    """Render a template file with {{VAR}} substitutions to dest."""
    if not src.exists():
        print(f"[warn] template missing: {src}", file=sys.stderr)
        return False
    try:
        text = src.read_text(encoding="utf-8")
    except OSError as e:
        print(f"[warn] could not read {src}: {e}", file=sys.stderr)
        return False
    for key, value in variables.items():
        text = text.replace("{{" + key + "}}", value)
    try:
        dest.write_text(text, encoding="utf-8")
    except OSError as e:
        print(f"[warn] could not write {dest}: {e}", file=sys.stderr)
        return False
    return True


def _error(message, as_json=False):
    if as_json:
        print(json.dumps({"status": "error", "message": message}))
    else:
        print(f"[error] {message}", file=sys.stderr)
    sys.exit(1)


def init_vault(vault_path, topic, tool, force, as_json=False):
    """Bootstrap a new LLM Wiki vault at vault_path."""
    if vault_path.exists() and any(vault_path.iterdir()) and not force:
        _error(f"{vault_path} is not empty. Use --force to overwrite.", as_json)

    try:
        vault_path.mkdir(parents=True, exist_ok=True)
        for d in VAULT_DIRS:
            (vault_path / d).mkdir(parents=True, exist_ok=True)
    except OSError as e:
        _error(f"failed to create vault structure: {e}", as_json)

    today = dt.date.today().isoformat()
    variables = {
        "TOPIC": topic,
        "DATE": today,
        "VAULT_NAME": vault_path.name,
    }

    installed_files = []

    # Schema files (CLAUDE.md / AGENTS.md / .cursorrules)
    for spec in TOOL_FILES.get(tool, TOOL_FILES["claude-code"]):
        src_name, dest_name = spec.split(":", 1)
        dest = vault_path / dest_name
        if render_template(ASSETS_DIR / src_name, dest, variables):
            installed_files.append(dest_name)

    # Index + log seeds
    for spec in [
        ("index.md.template", vault_path / "wiki" / "index.md"),
        ("log.md.template", vault_path / "wiki" / "log.md"),
    ]:
        if render_template(ASSETS_DIR / spec[0], spec[1], variables):
            installed_files.append(str(spec[1].relative_to(vault_path)))

    # Page templates (reference copies inside the vault)
    tmpl_dest = vault_path / "wiki" / ".templates"
    tmpl_dest.mkdir(exist_ok=True)
    src_tmpl = ASSETS_DIR / "page-templates"
    template_count = 0
    if src_tmpl.exists():
        for f in src_tmpl.iterdir():
            if f.is_file():
                try:
                    (tmpl_dest / f.name).write_text(
                        f.read_text(encoding="utf-8"), encoding="utf-8"
                    )
                    template_count += 1
                except OSError as e:
                    print(f"[warn] failed to copy template {f.name}: {e}", file=sys.stderr)

    # .gitignore — exclude Obsidian workspace files
    gitignore = vault_path / ".gitignore"
    gitignore.write_text(
        "\n".join([".obsidian/workspace*", ".obsidian/cache", ".DS_Store", ""]),
        encoding="utf-8",
    )

    result = {
        "status": "ok",
        "vault_path": str(vault_path),
        "topic": topic,
        "tool": tool,
        "date": today,
        "installed_files": installed_files,
        "page_templates_copied": template_count,
        "layers": {
            "raw": "your sources — immutable",
            "wiki": "LLM-maintained knowledge base",
            "index": "wiki/index.md",
            "log": "wiki/log.md",
        },
        "next_steps": [
            "Open the vault in Obsidian",
            "Drop a source into raw/",
            "Run /wiki-ingest <path> in your LLM CLI",
        ],
    }

    if as_json:
        print(json.dumps(result, indent=2))
        return result

    print(f"[ok] Initialized LLM Wiki vault at: {vault_path}")
    print(f"     Topic: {topic}")
    print(f"     Tool: {tool}")
    print(f"     Installed: {', '.join(installed_files)}")
    print(f"     Page templates copied: {template_count}")
    print("     Layers:")
    print("       raw/          (your sources — immutable)")
    print("       wiki/         (LLM-maintained knowledge base)")
    print("       wiki/index.md (catalog)")
    print("       wiki/log.md   (timeline)")
    print()
    print("Next steps:")
    print("  1. Open the vault in Obsidian")
    print("  2. Drop a source into raw/")
    print("  3. Run /wiki-ingest <path> in your LLM CLI")
    return result


def main():
    p = argparse.ArgumentParser(
        description="Initialize an LLM Wiki vault — the three-layer structure (raw/, wiki/, schema) Karpathy describes in the LLM Wiki gist.",
    )
    p.add_argument("--path", required=True, help="Vault directory to create/initialize")
    p.add_argument(
        "--topic",
        required=True,
        help="Short description of what this wiki is about (e.g. 'LLM interpretability')",
    )
    p.add_argument(
        "--tool",
        default="all",
        choices=sorted(TOOL_FILES.keys()),
        help="Which schema file(s) to install (default: all)",
    )
    p.add_argument(
        "--force", action="store_true", help="Overwrite non-empty target directory"
    )
    p.add_argument(
        "--json", action="store_true", help="Emit result as JSON instead of human-readable"
    )
    args = p.parse_args()
    init_vault(
        Path(args.path).expanduser().resolve(),
        args.topic,
        args.tool,
        args.force,
        as_json=args.json,
    )


if __name__ == "__main__":
    main()
