#!/usr/bin/env python3
"""
export_marp.py — Render a wiki page (or subtree) as a Marp slide deck.

Marp is a Markdown-based slide format supported by an Obsidian plugin. This
script adds Marp frontmatter and converts `## H2` headings into slide breaks,
so any wiki page with H2 sections becomes a usable slide deck with zero
manual formatting.

Usage:
    python export_marp.py --vault . --page wiki/synthesis/interpretability-overview.md
    python export_marp.py --vault . --page wiki/concepts/ --theme gaia --out slides/
"""
from __future__ import annotations
import argparse
import json
import re
import sys
from pathlib import Path

FRONTMATTER_RE = re.compile(r"^---\s*\n(.*?)\n---\s*\n", re.DOTALL)

MARP_HEADER = """---
marp: true
theme: {theme}
paginate: true
---

"""


def strip_frontmatter(text: str) -> str:
    return FRONTMATTER_RE.sub("", text, count=1)


def to_marp(text: str, theme: str) -> str:
    body = strip_frontmatter(text).strip()
    # Turn each "## " into a new slide separator.
    # First H1 → title slide. Subsequent H2 → slide breaks.
    lines = body.splitlines()
    out: list[str] = []
    seen_h1 = False
    for line in lines:
        if line.startswith("# ") and not seen_h1:
            out.append(line)
            out.append("")
            seen_h1 = True
            continue
        if line.startswith("## "):
            out.append("\n---\n")
            out.append(line)
            continue
        out.append(line)
    return MARP_HEADER.format(theme=theme) + "\n".join(out).strip() + "\n"


def render_one(src, out_path, theme, verbose=True):
    """Render a single markdown page as a Marp slide deck."""
    try:
        text = src.read_text(encoding="utf-8", errors="replace")
    except OSError as e:
        raise RuntimeError(f"failed to read {src}: {e}")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        out_path.write_text(to_marp(text, theme), encoding="utf-8")
    except OSError as e:
        raise RuntimeError(f"failed to write {out_path}: {e}")
    if verbose:
        print(f"[ok] {src.name} -> {out_path}")
    return out_path


def _error(message, as_json=False):
    if as_json:
        print(json.dumps({"status": "error", "message": message}))
    else:
        print(f"[error] {message}", file=sys.stderr)
    sys.exit(1)


def main():
    p = argparse.ArgumentParser(
        description="Render a wiki page (or subtree) to a Marp slide deck.",
        epilog="Marp is a Markdown-based slide format supported by an Obsidian plugin.",
    )
    p.add_argument("--vault", required=True, help="Vault root directory")
    p.add_argument(
        "--page",
        required=True,
        help="Page or directory relative to the vault (e.g. wiki/synthesis/overview.md)",
    )
    p.add_argument(
        "--theme", default="default", choices=["default", "gaia", "uncover"], help="Marp theme"
    )
    p.add_argument(
        "--out", default="slides", help="Output directory relative to vault (default: slides)"
    )
    p.add_argument(
        "--json", action="store_true", help="Emit result as JSON instead of human-readable"
    )
    args = p.parse_args()

    vault = Path(args.vault).expanduser().resolve()
    if not vault.exists():
        _error(f"vault does not exist: {vault}", args.json)

    src = (vault / args.page).resolve()
    if not src.exists():
        _error(f"page not found: {src}", args.json)

    out_root = vault / args.out
    rendered = []

    try:
        if src.is_file():
            dest = out_root / src.name.replace(".md", ".marp.md")
            render_one(src, dest, args.theme, verbose=not args.json)
            rendered.append(str(dest.relative_to(vault)))
        else:
            for md in sorted(src.rglob("*.md")):
                rel = md.relative_to(src)
                dest = out_root / rel.with_suffix(".marp.md")
                render_one(md, dest, args.theme, verbose=not args.json)
                rendered.append(str(dest.relative_to(vault)))
    except RuntimeError as e:
        _error(str(e), args.json)

    if args.json:
        print(
            json.dumps(
                {
                    "status": "ok",
                    "vault": str(vault),
                    "source": str(src.relative_to(vault)),
                    "theme": args.theme,
                    "output_dir": args.out,
                    "rendered_count": len(rendered),
                    "rendered": rendered,
                },
                indent=2,
            )
        )


if __name__ == "__main__":
    main()
