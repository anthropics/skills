#!/usr/bin/env python3
"""Generate a compact onboarding summary for a codebase (stdlib only)."""

from __future__ import annotations

import argparse
import json
import os
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List

IGNORED_DIRS = {
    ".git",
    "node_modules",
    ".next",
    "dist",
    "build",
    "coverage",
    "venv",
    ".venv",
    "__pycache__",
}

EXT_TO_LANG = {
    ".py": "Python",
    ".ts": "TypeScript",
    ".tsx": "TypeScript",
    ".js": "JavaScript",
    ".jsx": "JavaScript",
    ".go": "Go",
    ".rs": "Rust",
    ".java": "Java",
    ".kt": "Kotlin",
    ".rb": "Ruby",
    ".php": "PHP",
    ".cs": "C#",
    ".c": "C",
    ".cpp": "C++",
    ".h": "C/C++",
    ".swift": "Swift",
    ".sql": "SQL",
    ".sh": "Shell",
}

KEY_CONFIG_FILES = [
    "package.json",
    "pnpm-workspace.yaml",
    "turbo.json",
    "nx.json",
    "lerna.json",
    "tsconfig.json",
    "next.config.js",
    "next.config.mjs",
    "pyproject.toml",
    "requirements.txt",
    "go.mod",
    "Cargo.toml",
    "docker-compose.yml",
    "Dockerfile",
    ".github/workflows",
]


def iter_files(root: Path) -> Iterable[Path]:
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in IGNORED_DIRS]
        for name in filenames:
            path = Path(dirpath) / name
            if path.is_file():
                yield path


def detect_languages(paths: Iterable[Path]) -> Dict[str, int]:
    counts: Counter[str] = Counter()
    for path in paths:
        lang = EXT_TO_LANG.get(path.suffix.lower())
        if lang:
            counts[lang] += 1
    return dict(sorted(counts.items(), key=lambda item: (-item[1], item[0])))


def find_key_configs(root: Path) -> List[str]:
    found: List[str] = []
    for rel in KEY_CONFIG_FILES:
        if (root / rel).exists():
            found.append(rel)
    return found


def top_level_structure(root: Path, max_depth: int) -> List[str]:
    lines: List[str] = []
    for dirpath, dirnames, filenames in os.walk(root):
        rel = Path(dirpath).relative_to(root)
        depth = 0 if str(rel) == "." else len(rel.parts)
        if depth > max_depth:
            dirnames[:] = []
            continue

        if any(part in IGNORED_DIRS for part in rel.parts):
            dirnames[:] = []
            continue

        indent = "  " * depth
        if str(rel) != ".":
            lines.append(f"{indent}{rel.name}/")

        visible_files = [f for f in sorted(filenames) if not f.startswith(".")]
        for filename in visible_files[:10]:
            lines.append(f"{indent}  {filename}")

        dirnames[:] = sorted([d for d in dirnames if d not in IGNORED_DIRS])
    return lines


def build_report(root: Path, max_depth: int) -> Dict[str, object]:
    files = list(iter_files(root))
    languages = detect_languages(files)
    total_files = len(files)
    file_count_by_ext: Counter[str] = Counter(p.suffix.lower() or "<no-ext>" for p in files)

    largest = sorted(
        ((str(p.relative_to(root)), p.stat().st_size) for p in files),
        key=lambda item: item[1],
        reverse=True,
    )[:20]

    return {
        "root": str(root),
        "file_count": total_files,
        "languages": languages,
        "key_config_files": find_key_configs(root),
        "top_extensions": dict(file_count_by_ext.most_common(12)),
        "largest_files": largest,
        "directory_structure": top_level_structure(root, max_depth),
    }


def format_size(num_bytes: int) -> str:
    units = ["B", "KB", "MB", "GB"]
    value = float(num_bytes)
    for unit in units:
        if value < 1024 or unit == units[-1]:
            return f"{value:.1f}{unit}"
        value /= 1024
    return f"{num_bytes}B"


def print_text(report: Dict[str, object]) -> None:
    print("Codebase Onboarding Summary")
    print(f"Root: {report['root']}")
    print(f"Total files: {report['file_count']}")
    print("")

    print("Languages detected")
    if report["languages"]:
        for lang, count in report["languages"].items():
            print(f"- {lang}: {count}")
    else:
        print("- No recognized source file extensions")
    print("")

    print("Key config files")
    configs = report["key_config_files"]
    if configs:
        for cfg in configs:
            print(f"- {cfg}")
    else:
        print("- None found from default checklist")
    print("")

    print("Largest files")
    for rel, size in report["largest_files"][:10]:
        print(f"- {rel}: {format_size(size)}")
    print("")

    print("Directory structure")
    for line in report["directory_structure"][:200]:
        print(line)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Scan a repository and generate onboarding summary facts.")
    parser.add_argument("path", help="Path to project directory")
    parser.add_argument("--max-depth", type=int, default=2, help="Max depth for structure output (default: 2)")
    parser.add_argument("--json", action="store_true", help="Print JSON output")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = Path(args.path).expanduser().resolve()
    if not root.exists() or not root.is_dir():
        raise SystemExit(f"Path is not a directory: {root}")

    report = build_report(root, max_depth=max(1, args.max_depth))
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print_text(report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
