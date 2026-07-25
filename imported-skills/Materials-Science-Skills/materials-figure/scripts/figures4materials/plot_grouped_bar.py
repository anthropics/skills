#!/usr/bin/env python3
"""Generic grouped-bar script for COLUMN_MAP driven datasets."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from _script_helpers import load_mapped_data


COLUMN_MAP = {
    "x_labels": {"column": "sample"},
    "series": [{"key": "value", "column": "value"}],
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", required=True)
    parser.add_argument("--column-map")
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()

    column_map = json.loads(args.column_map) if args.column_map else COLUMN_MAP
    mapped = load_mapped_data(args.data, column_map)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "mapped_data.json").write_text(
        json.dumps(mapped, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
