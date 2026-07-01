#!/usr/bin/env python3
"""
Render a simple Obsidian Canvas overview for an ECL v2 bundle.
"""

from __future__ import annotations

import argparse
import json
import secrets
import sys
from pathlib import Path

FILES = [
    "00-overview.md",
    "05-constraint-ledger.md",
    "10-a-preprocess.md",
    "20-b-divergence.md",
    "30-c-requirements.md",
    "40-d-critique.md",
    "50-e-closure.md",
    "60-f-probes.md",
    "70-g-red-blue.md",
    "80-h-review.md",
    "90-code-handoff.md",
]


def make_id() -> str:
    return secrets.token_hex(8)


def find_vault_root(path: Path) -> Path | None:
    for candidate in [path, *path.parents]:
        if (candidate / ".obsidian").exists():
            return candidate
    return None


def vault_relative(path: Path, bundle_dir: Path) -> str:
    vault_root = find_vault_root(bundle_dir)
    if vault_root is None:
        return path.name
    return path.relative_to(vault_root).as_posix()


def main() -> int:
    parser = argparse.ArgumentParser(description="Render a simple canvas for an ECL v2 bundle.")
    parser.add_argument("bundle_dir", help="Bundle directory containing the ECL notes")
    parser.add_argument("--output", help="Optional canvas path. Defaults to 00-overview-map.canvas inside the bundle.")
    args = parser.parse_args()

    bundle_dir = Path(args.bundle_dir).expanduser().resolve()
    if not bundle_dir.exists():
        print(f"[ERROR] Bundle directory not found: {bundle_dir}")
        return 1

    missing = [filename for filename in FILES if not (bundle_dir / filename).exists()]
    if missing:
        print("[ERROR] Cannot render canvas because these files are missing:")
        for filename in missing:
            print(f"  - {filename}")
        return 1

    output_path = (
        Path(args.output).expanduser().resolve()
        if args.output
        else bundle_dir / "00-overview-map.canvas"
    )

    layout = {
        "00-overview.md": (0, 220, 360, 220),
        "05-constraint-ledger.md": (420, 20, 360, 220),
        "10-a-preprocess.md": (420, 280, 320, 180),
        "20-b-divergence.md": (820, 280, 320, 180),
        "30-c-requirements.md": (1220, 280, 320, 180),
        "40-d-critique.md": (1620, 280, 320, 180),
        "50-e-closure.md": (2020, 280, 320, 180),
        "60-f-probes.md": (2420, 280, 320, 180),
        "70-g-red-blue.md": (2820, 280, 320, 180),
        "80-h-review.md": (3220, 280, 320, 180),
        "90-code-handoff.md": (3620, 220, 360, 220),
    }

    nodes = []
    edges = []
    by_file = {}
    for filename in FILES:
        node_id = make_id()
        by_file[filename] = node_id
        x, y, width, height = layout[filename]
        nodes.append(
            {
                "id": node_id,
                "type": "file",
                "x": x,
                "y": y,
                "width": width,
                "height": height,
                "file": vault_relative(bundle_dir / filename, bundle_dir),
            }
        )

    for first, second in zip(FILES, FILES[1:]):
        edges.append(
            {
                "id": make_id(),
                "fromNode": by_file[first],
                "fromSide": "right",
                "toNode": by_file[second],
                "toSide": "left",
                "toEnd": "arrow",
            }
        )

    output_path.write_text(json.dumps({"nodes": nodes, "edges": edges}, indent=2) + "\n", encoding="utf-8")
    print(f"[OK] Rendered canvas: {output_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
