#!/usr/bin/env python3
"""Check that the skill creator entrypoint fits common context budgets."""

from pathlib import Path

MAX_BYTES = 15 * 1024
ENTRYPOINT = Path(__file__).resolve().parents[1] / "SKILL.md"


def main() -> int:
    size = ENTRYPOINT.stat().st_size
    if size > MAX_BYTES:
        print(f"{ENTRYPOINT}: {size} bytes exceeds the {MAX_BYTES}-byte limit")
        return 1
    print(f"{ENTRYPOINT}: {size}/{MAX_BYTES} bytes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
