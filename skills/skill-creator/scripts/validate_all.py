#!/usr/bin/env python3
"""Repo-wide validation sweep for Agent Skills.

Runs the progressive-disclosure validator (quick_validate) over every
skill directory in the repo and exits non-zero if any skill fails. This
is the CI gate that keeps the #1487 failure class — an oversized SKILL.md
eager payload that blows the context window on trigger — from regressing.

Usage:
    python validate_all.py [--strict] [--json] [--skills-dir DIR]
                           [--max-lines N] [--max-tokens N]
                           [--max-payload-tokens N]

Exit code 0 if every skill passes, 1 otherwise (CI-friendly).
"""

import argparse
import json
import sys
from pathlib import Path

# Make quick_validate importable whether this runs as a script or module.
sys.path.insert(0, str(Path(__file__).resolve().parent))

from quick_validate import (  # noqa: E402
    DEFAULT_MAX_LINES,
    DEFAULT_MAX_PAYLOAD_TOKENS,
    DEFAULT_MAX_TOKENS,
    validate_skill_detailed,
)


def find_skills(skills_dir: Path) -> list[Path]:
    """Top-level skill directories (those containing a SKILL.md)."""
    return sorted(
        (d for d in skills_dir.iterdir() if d.is_dir() and (d / "SKILL.md").is_file()),
        key=lambda p: p.name,
    )


def sweep(
    skills_dir: Path,
    *,
    strict: bool,
    max_lines: int,
    max_tokens: int,
    max_payload_tokens: int,
) -> list:
    """Validate every skill directory and return the results."""
    results = []
    for skill_dir in find_skills(skills_dir):
        results.append(
            validate_skill_detailed(
                skill_dir,
                max_lines=max_lines,
                max_tokens=max_tokens,
                max_payload_tokens=max_payload_tokens,
                strict=strict,
            )
        )
    return results


def _row(result) -> dict:
    m = result.metrics
    return {
        "skill": result.skill_path.name,
        "valid": result.valid,
        "skill_md_chars": m.get("skill_md_chars", 0),
        "skill_md_lines": m.get("skill_md_lines", 0),
        "skill_md_tokens": m.get("skill_md_tokens", 0),
        "payload_tokens": m.get("payload_tokens", 0),
        "bundled_md_files": m.get("bundled_md_files", 0),
        "warnings": sum(1 for f in result.findings if f.level == "warning"),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate every skill in the repo")
    parser.add_argument(
        "--skills-dir",
        default=None,
        help="Directory containing skill folders (default: <repo root>/skills)",
    )
    parser.add_argument("--strict", action="store_true", help="Treat budget overruns as errors")
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON")
    parser.add_argument("--max-lines", type=int, default=DEFAULT_MAX_LINES)
    parser.add_argument("--max-tokens", type=int, default=DEFAULT_MAX_TOKENS)
    parser.add_argument("--max-payload-tokens", type=int, default=DEFAULT_MAX_PAYLOAD_TOKENS)
    args = parser.parse_args(argv)

    repo_root = Path(__file__).resolve().parents[3]
    skills_dir = Path(args.skills_dir) if args.skills_dir else repo_root / "skills"

    results = sweep(
        skills_dir,
        strict=args.strict,
        max_lines=args.max_lines,
        max_tokens=args.max_tokens,
        max_payload_tokens=args.max_payload_tokens,
    )

    if args.json:
        print(json.dumps(
            {"results": [_row(r) for r in results], "all_valid": all(r.valid for r in results)},
            indent=2,
        ))
    else:
        header = (
            f"{'skill':<24} {'valid':<6} {'chars':>8} {'lines':>5} "
            f"{'tokens':>7} {'payload':>8} {'bundled':>7} {'warn':>4}"
        )
        print(header)
        print("-" * len(header))
        for r in results:
            m = r.metrics
            print(
                f"{r.skill_path.name:<24} "
                f"{'OK' if r.valid else 'FAIL':<6} "
                f"{m.get('skill_md_chars', 0):>8,} "
                f"{m.get('skill_md_lines', 0):>5} "
                f"{m.get('skill_md_tokens', 0):>7,} "
                f"{m.get('payload_tokens', 0):>8,} "
                f"{m.get('bundled_md_files', 0):>7} "
                f"{sum(1 for f in r.findings if f.level == 'warning'):>4}"
            )
        failed = [r for r in results if not r.valid]
        if failed:
            print(f"\n{len(failed)} skill(s) failed strict validation:")
            for r in failed:
                for f in r.findings:
                    if f.level == "error":
                        print(f"  ❌ {r.skill_path.name}: [{f.check}] {f.message}")
        print(f"\n{len(results) - len(failed)}/{len(results)} skills valid")

    return 1 if any(not r.valid for r in results) else 0


if __name__ == "__main__":
    sys.exit(main())
