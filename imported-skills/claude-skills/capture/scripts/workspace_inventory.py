#!/usr/bin/env python3
"""workspace_inventory.py — Glob+Grep helper for capture's Section 3 (Connections).

Stdlib-only. Given a working directory + a list of dump-derived keywords,
returns a structured inventory that the capture skill can use to surface
real workspace connections (never fabricated).

What it returns:
  1. Per-keyword filename matches (Glob-style)
  2. Per-keyword content matches (line-grep across source files)
  3. Top-level folder structure (max-depth 2)

What it does NOT do:
  - Score relevance (capture skill applies judgment on top)
  - Fabricate matches (only real Glob/Grep results)
  - Make LLM calls

Usage:
    python workspace_inventory.py --root . --keywords "auth,login,2fa"
    python workspace_inventory.py --root . --keywords "skill,megaprompt" --output json
    python workspace_inventory.py --sample
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Set


DEFAULT_SOURCE_EXTENSIONS = {
    ".py", ".ts", ".tsx", ".js", ".jsx", ".go", ".java", ".kt", ".rb",
    ".cs", ".rs", ".swift", ".php", ".scala", ".clj", ".ex", ".exs",
    ".md", ".mdx", ".rst", ".txt", ".json", ".yaml", ".yml", ".toml",
}
DEFAULT_EXCLUDE_DIRS = {
    "node_modules", ".git", "dist", "build", "target",
    ".venv", "venv", "__pycache__", ".next", ".cache",
}
MAX_FILENAME_MATCHES_PER_KEYWORD = 20
MAX_CONTENT_MATCHES_PER_KEYWORD = 10
MAX_FOLDER_DEPTH = 2


SAMPLE_TREE: Dict[str, str] = {
    "src/auth/login.ts": "// auth login flow handler\nexport function login() {}\n",
    "src/auth/2fa.ts": "// 2fa stub\nexport function setup2FA() {}\n",
    "src/users/profile.ts": "// user profile\nexport function getProfile() {}\n",
    "docs/auth-bugs.md": "# Auth bugs\n\n- The login race condition is back.\n",
    "tests/auth.test.ts": "// auth tests\ndescribe('auth', () => {});\n",
    "README.md": "# project\n\nAuth + login + users.\n",
}


def collect_files(root: Path, source_extensions: Set[str], exclude_dirs: Set[str]) -> List[Path]:
    found: List[Path] = []
    for p in root.rglob("*"):
        if p.is_dir():
            continue
        if any(part in exclude_dirs for part in p.parts):
            continue
        if p.suffix.lower() in source_extensions:
            found.append(p)
    return found


def filename_matches(files: List[Path], keyword: str) -> List[str]:
    kw = keyword.lower()
    out: List[str] = []
    for p in files:
        if kw in p.name.lower():
            out.append(str(p))
        if len(out) >= MAX_FILENAME_MATCHES_PER_KEYWORD:
            break
    return out


def content_matches(files: List[Path], keyword: str) -> List[Dict[str, Any]]:
    pattern = re.compile(re.escape(keyword), re.IGNORECASE)
    out: List[Dict[str, Any]] = []
    for p in files:
        try:
            text = p.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        for line_no, line in enumerate(text.splitlines(), start=1):
            if pattern.search(line):
                out.append({
                    "file": str(p),
                    "line": line_no,
                    "snippet": line.strip()[:120],
                })
                if len(out) >= MAX_CONTENT_MATCHES_PER_KEYWORD:
                    return out
    return out


def folder_structure(root: Path, max_depth: int, exclude_dirs: Set[str]) -> List[str]:
    out: List[str] = []
    root = root.resolve()
    for p in root.rglob("*"):
        if not p.is_dir():
            continue
        if any(part in exclude_dirs for part in p.parts):
            continue
        try:
            rel = p.relative_to(root)
        except ValueError:
            continue
        depth = len(rel.parts)
        if 0 < depth <= max_depth:
            out.append(str(rel))
    return sorted(out)


def inventory(
    root: Path,
    keywords: List[str],
    source_extensions: Set[str],
    exclude_dirs: Set[str],
) -> Dict[str, Any]:
    files = collect_files(root, source_extensions, exclude_dirs)
    per_keyword: Dict[str, Dict[str, Any]] = {}
    for kw in keywords:
        per_keyword[kw] = {
            "filename_matches": filename_matches(files, kw),
            "content_matches": content_matches(files, kw),
        }
    return {
        "root": str(root.resolve()),
        "files_scanned": len(files),
        "folder_structure": folder_structure(root, MAX_FOLDER_DEPTH, exclude_dirs),
        "per_keyword": per_keyword,
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Workspace inventory for: {result['root']}")
    out.append(f"  Files scanned: {result['files_scanned']}")
    out.append("")
    out.append("Folder structure (max depth 2):")
    for f in result["folder_structure"][:30]:
        out.append(f"  - {f}/")
    if len(result["folder_structure"]) > 30:
        out.append(f"  ... + {len(result['folder_structure']) - 30} more")
    out.append("")
    for kw, hits in result["per_keyword"].items():
        out.append(f"Keyword: '{kw}'")
        if hits["filename_matches"]:
            out.append(f"  Filename matches ({len(hits['filename_matches'])}):")
            for f in hits["filename_matches"]:
                out.append(f"    - {f}")
        else:
            out.append("  Filename matches: (none)")
        if hits["content_matches"]:
            out.append(f"  Content matches ({len(hits['content_matches'])}):")
            for m in hits["content_matches"]:
                out.append(f"    - {m['file']}:{m['line']}  {m['snippet']}")
        else:
            out.append("  Content matches: (none)")
        out.append("")
    return "\n".join(out)


def run_sample(keywords: List[str]) -> Dict[str, Any]:
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        for rel, content in SAMPLE_TREE.items():
            p = root / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(content, encoding="utf-8")
        return inventory(root, keywords, DEFAULT_SOURCE_EXTENSIONS, DEFAULT_EXCLUDE_DIRS)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--root", help="Root directory to inventory")
    parser.add_argument("--keywords", help="Comma-separated keywords to search for")
    parser.add_argument("--extensions", help="Comma-separated source extensions (default: common)")
    parser.add_argument("--sample", action="store_true", help="Inventory the embedded sample tree")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        sample_keywords = ["auth", "login", "2fa"] if not args.keywords else [k.strip() for k in args.keywords.split(",") if k.strip()]
        result = run_sample(sample_keywords)
    elif args.root and args.keywords:
        root = Path(args.root)
        if not root.exists():
            print(f"error: {args.root} not found", file=sys.stderr)
            return 2
        kws = [k.strip() for k in args.keywords.split(",") if k.strip()]
        if not kws:
            print("error: --keywords must list at least one keyword", file=sys.stderr)
            return 2
        if args.extensions:
            exts = {e.strip() if e.strip().startswith(".") else "." + e.strip() for e in args.extensions.split(",")}
        else:
            exts = DEFAULT_SOURCE_EXTENSIONS
        result = inventory(root, kws, exts, DEFAULT_EXCLUDE_DIRS)
    else:
        parser.print_help()
        return 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
