#!/usr/bin/env python3
"""
LOC Guard.

Portable file-length checker for agent-assisted development.

Default policy:
- warn above 400 counted LOC;
- fail above 600 counted LOC.

Counted LOC defaults to non-blank physical lines. Comments are counted by default.
"""

from __future__ import annotations

import argparse
import fnmatch
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DEFAULT_WARN_AT = 400
DEFAULT_FAIL_AT = 600
DEFAULT_INCLUDE_EXTENSIONS = {
    ".cs", ".cshtml", ".razor",
    ".js", ".jsx", ".ts", ".tsx",
    ".py", ".java", ".go", ".rs",
    ".cpp", ".c", ".h", ".hpp",
    ".css", ".scss", ".html",
    ".sql", ".sh", ".ps1",
}
DEFAULT_EXCLUDES = [
    "**/.git/**",
    "**/.vs/**",
    "**/.idea/**",
    "**/.vscode/**",
    "**/bin/**",
    "**/obj/**",
    "**/node_modules/**",
    "**/dist/**",
    "**/build/**",
    "**/coverage/**",
    "**/generated/**",
    "**/Generated/**",
    "**/vendor/**",
    "**/Vendor/**",
    "**/Migrations/**",
    "**/*.g.cs",
    "**/*.generated.cs",
    "**/*.Designer.cs",
    "**/*.designer.cs",
    "**/*.min.js",
    "**/*.min.css",
]


SINGLE_LINE_COMMENT_PREFIXES = {
    ".cs": ["//"],
    ".cshtml": ["@*"],
    ".razor": ["@*", "//"],
    ".js": ["//"],
    ".jsx": ["//"],
    ".ts": ["//"],
    ".tsx": ["//"],
    ".py": ["#"],
    ".java": ["//"],
    ".go": ["//"],
    ".rs": ["//"],
    ".cpp": ["//"],
    ".c": ["//"],
    ".h": ["//"],
    ".hpp": ["//"],
    ".css": ["/*"],
    ".scss": ["//", "/*"],
    ".html": ["<!--"],
    ".sql": ["--"],
    ".sh": ["#"],
    ".ps1": ["#"],
}


@dataclass(frozen=True)
class AllowedLargeFile:
    path: str
    reason: str


@dataclass(frozen=True)
class Config:
    warn_at: int
    fail_at: int
    count_blank_lines: bool
    count_comment_lines: bool
    include_extensions: set[str]
    exclude: list[str]
    allowed_large_files: list[AllowedLargeFile]


@dataclass(frozen=True)
class FileResult:
    path: str
    counted_loc: int
    status: str
    reason: str | None = None


def main() -> int:
    parser = argparse.ArgumentParser(description="Check source files against LOC policy.")
    parser.add_argument("paths", nargs="*", default=["."], help="Files or directories to inspect.")
    parser.add_argument("--config", help="Path to loc-guard.config.json.")
    parser.add_argument("--warn", type=int, help="Override warning threshold.")
    parser.add_argument("--fail", type=int, help="Override failure threshold.")
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON.")
    parser.add_argument("--changed-only", action="store_true", help="Only inspect git changed files.")
    parser.add_argument("--staged", action="store_true", help="Only inspect git staged files.")
    parser.add_argument("--include", action="append", default=[], help="Extra extension to include, such as .md.")
    parser.add_argument("--exclude", action="append", default=[], help="Extra glob pattern to exclude.")
    parser.add_argument("--count-blank-lines", action="store_true", help="Count blank lines.")
    parser.add_argument("--ignore-comment-lines", action="store_true", help="Do not count simple comment-only lines.")

    args = parser.parse_args()

    try:
        config = load_config(args)
        root = find_repo_root(Path.cwd())
        files = collect_files(args, config, root)
        results = evaluate_files(files, config, root)
        if args.json:
            print_json(results, config)
        else:
            print_text(results, config)
        return exit_code(results)
    except Exception as exc:
        if args.json:
            print(json.dumps({"error": str(exc)}, indent=2))
        else:
            print(f"LOC Guard error: {exc}", file=sys.stderr)
        return 3


def load_config(args: argparse.Namespace) -> Config:
    data: dict[str, Any] = {}

    config_path = args.config
    if config_path:
        path = Path(config_path)
        if not path.exists():
            raise FileNotFoundError(f"config file not found: {config_path}")
        data = json.loads(path.read_text(encoding="utf-8"))
    else:
        auto = Path(".agent-tools/loc-guard.config.json")
        if auto.exists():
            data = json.loads(auto.read_text(encoding="utf-8"))

    warn_at = int(args.warn or data.get("warnAt", DEFAULT_WARN_AT))
    fail_at = int(args.fail or data.get("failAt", DEFAULT_FAIL_AT))
    if warn_at >= fail_at:
        raise ValueError("warn threshold must be lower than fail threshold")

    include_extensions = set(data.get("includeExtensions", list(DEFAULT_INCLUDE_EXTENSIONS)))
    include_extensions.update(args.include)
    include_extensions = {normalise_extension(ext) for ext in include_extensions}

    exclude = list(data.get("exclude", DEFAULT_EXCLUDES))
    exclude.extend(args.exclude)

    allowed = [
        AllowedLargeFile(
            path=str(item.get("path", "")).replace("\\", "/"),
            reason=str(item.get("reason", "")),
        )
        for item in data.get("allowedLargeFiles", [])
    ]
    allowed = [item for item in allowed if item.path]

    count_blank_lines = bool(data.get("countBlankLines", False)) or bool(args.count_blank_lines)
    count_comment_lines = bool(data.get("countCommentLines", True))
    if args.ignore_comment_lines:
        count_comment_lines = False

    return Config(
        warn_at=warn_at,
        fail_at=fail_at,
        count_blank_lines=count_blank_lines,
        count_comment_lines=count_comment_lines,
        include_extensions=include_extensions,
        exclude=exclude,
        allowed_large_files=allowed,
    )


def normalise_extension(value: str) -> str:
    value = value.strip()
    if not value:
        return value
    return value if value.startswith(".") else f".{value}"


def find_repo_root(start: Path) -> Path:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=start,
            check=True,
            text=True,
            capture_output=True,
        )
        return Path(result.stdout.strip()).resolve()
    except Exception:
        return start.resolve()


def collect_files(args: argparse.Namespace, config: Config, root: Path) -> list[Path]:
    if args.changed_only and args.staged:
        raise ValueError("use either --changed-only or --staged, not both")

    if args.changed_only or args.staged:
        files = git_files(root, staged=args.staged)
    else:
        files = expand_paths([Path(p) for p in args.paths])

    filtered: list[Path] = []
    for file_path in files:
        resolved = file_path if file_path.is_absolute() else (Path.cwd() / file_path)
        resolved = resolved.resolve()
        if not resolved.exists() or not resolved.is_file():
            continue
        if should_include(resolved, config, root):
            filtered.append(resolved)

    return sorted(set(filtered), key=lambda p: relative_path(p, root))


def git_files(root: Path, staged: bool) -> list[Path]:
    command = ["git", "diff", "--name-only", "--diff-filter=ACMR"]
    if staged:
        command.insert(2, "--cached")

    result = subprocess.run(command, cwd=root, check=True, text=True, capture_output=True)
    files = [root / line.strip() for line in result.stdout.splitlines() if line.strip()]

    if not staged:
        untracked = subprocess.run(
            ["git", "ls-files", "--others", "--exclude-standard"],
            cwd=root,
            check=True,
            text=True,
            capture_output=True,
        )
        files.extend(root / line.strip() for line in untracked.stdout.splitlines() if line.strip())

    return files


def expand_paths(paths: list[Path]) -> list[Path]:
    files: list[Path] = []

    for path in paths:
        if path.is_file():
            files.append(path)
        elif path.is_dir():
            for current_root, dir_names, file_names in os.walk(path):
                dir_names[:] = [name for name in dir_names if name not in {".git", "node_modules", "bin", "obj"}]
                for file_name in file_names:
                    files.append(Path(current_root) / file_name)

    return files


def should_include(path: Path, config: Config, root: Path) -> bool:
    if path.suffix not in config.include_extensions:
        return False

    rel = relative_path(path, root)
    rel_with_prefix = f"./{rel}"

    for pattern in config.exclude:
        normalised = pattern.replace("\\", "/")
        if fnmatch.fnmatch(rel, normalised) or fnmatch.fnmatch(rel_with_prefix, normalised):
            return False

    return True


def evaluate_files(files: list[Path], config: Config, root: Path) -> list[FileResult]:
    results: list[FileResult] = []

    for path in files:
        rel = relative_path(path, root)
        counted = count_loc(path, config)
        allowed = find_allowed_large_file(rel, config)

        if allowed and counted > config.warn_at:
            status = "exempt"
            reason = allowed.reason
        elif counted > config.fail_at:
            status = "fail"
            reason = None
        elif counted > config.warn_at:
            status = "warn"
            reason = None
        else:
            status = "ok"
            reason = None

        results.append(FileResult(rel, counted, status, reason))

    return results


def count_loc(path: Path, config: Config) -> int:
    count = 0
    prefixes = SINGLE_LINE_COMMENT_PREFIXES.get(path.suffix, [])

    with path.open("r", encoding="utf-8", errors="ignore") as handle:
        for raw_line in handle:
            line = raw_line.rstrip("\n\r")
            stripped = line.strip()

            if not config.count_blank_lines and not stripped:
                continue

            if not config.count_comment_lines and is_simple_comment_line(stripped, prefixes):
                continue

            count += 1

    return count


def is_simple_comment_line(stripped: str, prefixes: list[str]) -> bool:
    if not stripped:
        return False
    return any(stripped.startswith(prefix) for prefix in prefixes)


def find_allowed_large_file(rel: str, config: Config) -> AllowedLargeFile | None:
    for item in config.allowed_large_files:
        pattern = item.path.replace("\\", "/")
        if rel == pattern or fnmatch.fnmatch(rel, pattern):
            return item
    return None


def print_json(results: list[FileResult], config: Config) -> None:
    payload = {
        "warnAt": config.warn_at,
        "failAt": config.fail_at,
        "summary": summary(results),
        "files": [
            {
                "path": result.path,
                "countedLoc": result.counted_loc,
                "status": result.status,
                "reason": result.reason,
            }
            for result in results
        ],
    }
    print(json.dumps(payload, indent=2))


def print_text(results: list[FileResult], config: Config) -> None:
    data = summary(results)

    print("LOC Guard Report")
    print()
    print(f"Checked files: {data['checked']}")
    print(f"Soft warning threshold: {config.warn_at}")
    print(f"Hard failure threshold: {config.fail_at}")
    print()

    for status in ["fail", "warn", "exempt"]:
        matching = [result for result in results if result.status == status]
        if not matching:
            continue

        print(status.upper() + ":")
        for result in matching:
            print(f"- {result.path}")
            print(f"  Counted LOC: {result.counted_loc}")
            if result.reason:
                print(f"  Reason: {result.reason}")

            if status == "warn":
                print("  Required agent action:")
                print("  - inspect cohesion and responsibility boundaries")
                print("  - report either:")
                print("    warning accepted with justification: ...")
                print("    split performed because: ...")
            elif status == "fail":
                print("  Required agent action:")
                print("  - split/refactor below the hard cap, or")
                print("  - request explicit user approval for an exception")
        print()

    if data["fail"] == 0 and data["warn"] == 0:
        print("OK: no LOC warnings or failures.")


def summary(results: list[FileResult]) -> dict[str, int]:
    return {
        "checked": len(results),
        "ok": sum(1 for result in results if result.status == "ok"),
        "warn": sum(1 for result in results if result.status == "warn"),
        "fail": sum(1 for result in results if result.status == "fail"),
        "exempt": sum(1 for result in results if result.status == "exempt"),
    }


def exit_code(results: list[FileResult]) -> int:
    if any(result.status == "fail" for result in results):
        return 2
    if any(result.status == "warn" for result in results):
        return 1
    return 0


def relative_path(path: Path, root: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return path.resolve().as_posix()


if __name__ == "__main__":
    sys.exit(main())
