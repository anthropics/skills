#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import shutil
import sys


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Install the threejs-master GLTF calibration helper module into a project folder.",
    )
    parser.add_argument(
        "--out",
        required=True,
        help="Destination path (file) to write, e.g. ./gltf-calibration-helpers.mjs",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Overwrite if destination exists.",
    )
    args = parser.parse_args()

    src = pathlib.Path(__file__).resolve().parent / "gltf-calibration-helpers.mjs"
    if not src.exists():
        print(f"[ERR] Missing source module: {src}", file=sys.stderr)
        return 2

    dst = pathlib.Path(args.out).expanduser().resolve()
    dst.parent.mkdir(parents=True, exist_ok=True)

    if dst.exists() and not args.force:
        print(f"[ERR] Destination exists (use --force): {dst}", file=sys.stderr)
        return 2

    shutil.copyfile(src, dst)
    print(f"[OK] Wrote: {dst}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
