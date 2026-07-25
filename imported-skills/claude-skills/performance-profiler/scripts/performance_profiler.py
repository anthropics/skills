#!/usr/bin/env python3
"""Lightweight repo performance profiling helper (stdlib only)."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

EXT_WEIGHTS = {
    ".js": 1.0,
    ".jsx": 1.0,
    ".ts": 1.0,
    ".tsx": 1.0,
    ".css": 0.7,
    ".map": 2.0,
}


def iter_files(root: Path) -> Iterable[Path]:
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in {".git", "node_modules", ".next", "dist", "build", "coverage", "__pycache__"}]
        for filename in filenames:
            path = Path(dirpath) / filename
            if path.is_file():
                yield path


def get_large_files(root: Path, threshold_bytes: int) -> List[Tuple[str, int]]:
    large: List[Tuple[str, int]] = []
    for file_path in iter_files(root):
        size = file_path.stat().st_size
        if size >= threshold_bytes:
            large.append((str(file_path.relative_to(root)), size))
    return sorted(large, key=lambda item: item[1], reverse=True)


def count_dependencies(root: Path) -> Dict[str, int]:
    counts = {"node_dependencies": 0, "python_dependencies": 0, "go_dependencies": 0}

    package_json = root / "package.json"
    if package_json.exists():
        try:
            data = json.loads(package_json.read_text(encoding="utf-8"))
            deps = data.get("dependencies", {})
            dev_deps = data.get("devDependencies", {})
            counts["node_dependencies"] = len(deps) + len(dev_deps)
        except Exception:
            pass

    requirements = root / "requirements.txt"
    if requirements.exists():
        lines = [ln.strip() for ln in requirements.read_text(encoding="utf-8", errors="ignore").splitlines()]
        counts["python_dependencies"] = sum(1 for ln in lines if ln and not ln.startswith("#"))

    go_mod = root / "go.mod"
    if go_mod.exists():
        lines = go_mod.read_text(encoding="utf-8", errors="ignore").splitlines()
        in_require_block = False
        go_count = 0
        for ln in lines:
            s = ln.strip()
            if s.startswith("require ("):
                in_require_block = True
                continue
            if in_require_block and s == ")":
                in_require_block = False
                continue
            if in_require_block and s and not s.startswith("//"):
                go_count += 1
            elif s.startswith("require ") and not s.endswith("("):
                go_count += 1
        counts["go_dependencies"] = go_count

    return counts


def bundle_indicators(root: Path) -> Dict[str, object]:
    indicators = {
        "build_dirs_present": [],
        "bundle_like_files": 0,
        "estimated_bundle_weight": 0.0,
    }
    for d in ["dist", "build", ".next", "out"]:
        if (root / d).exists():
            indicators["build_dirs_present"].append(d)

    bundle_files = 0
    weight = 0.0
    for path in iter_files(root):
        ext = path.suffix.lower()
        if ext in EXT_WEIGHTS:
            bundle_files += 1
            size_kb = path.stat().st_size / 1024.0
            weight += size_kb * EXT_WEIGHTS[ext]

    indicators["bundle_like_files"] = bundle_files
    indicators["estimated_bundle_weight"] = round(weight, 2)
    return indicators


def format_size(num_bytes: int) -> str:
    units = ["B", "KB", "MB", "GB"]
    value = float(num_bytes)
    for unit in units:
        if value < 1024.0 or unit == units[-1]:
            return f"{value:.1f}{unit}"
        value /= 1024.0
    return f"{num_bytes}B"


def build_report(root: Path, threshold_bytes: int) -> Dict[str, object]:
    large = get_large_files(root, threshold_bytes)
    deps = count_dependencies(root)
    bundles = bundle_indicators(root)
    return {
        "root": str(root),
        "large_file_threshold_bytes": threshold_bytes,
        "large_files": large,
        "dependency_counts": deps,
        "bundle_indicators": bundles,
    }


def print_text(report: Dict[str, object]) -> None:
    print("Performance Profile Report")
    print(f"Root: {report['root']}")
    print(f"Large-file threshold: {format_size(int(report['large_file_threshold_bytes']))}")
    print("")

    dep_counts = report["dependency_counts"]
    print("Dependency Counts")
    print(f"- Node: {dep_counts['node_dependencies']}")
    print(f"- Python: {dep_counts['python_dependencies']}")
    print(f"- Go: {dep_counts['go_dependencies']}")
    print("")

    bundle = report["bundle_indicators"]
    print("Bundle Indicators")
    print(f"- Build directories present: {', '.join(bundle['build_dirs_present']) or 'none'}")
    print(f"- Bundle-like files: {bundle['bundle_like_files']}")
    print(f"- Estimated weighted bundle size: {bundle['estimated_bundle_weight']} KB")
    print("")

    print("Large Files")
    large_files = report["large_files"]
    if not large_files:
        print("- None above threshold")
    else:
        for rel_path, size in large_files[:20]:
            print(f"- {rel_path}: {format_size(size)}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Analyze a project directory for common performance risk indicators."
    )
    parser.add_argument("path", help="Directory to analyze")
    parser.add_argument(
        "--large-file-threshold-kb",
        type=int,
        default=512,
        help="Threshold in KB for reporting large files (default: 512)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Print JSON output instead of text",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = Path(args.path).expanduser().resolve()
    if not root.exists() or not root.is_dir():
        raise SystemExit(f"Path is not a directory: {root}")

    threshold = max(1, args.large_file_threshold_kb) * 1024
    report = build_report(root, threshold)

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print_text(report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
