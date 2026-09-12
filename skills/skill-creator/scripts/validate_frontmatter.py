#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.9"
# dependencies = [
#   "pyyaml>=6.0",
# ]
# ///
"""validate_frontmatter.py — Validate a SKILL.md frontmatter against the Agent Skills specification.

Checks every frontmatter field constraint defined at
https://agentskills.io/specification. Reports per-field PASS/FAIL with
specific error messages. Exits non-zero on any failure so it composes
cleanly with shell pipelines and CI.

USAGE
  scripts/validate_frontmatter.py [PATH] [--format text|json]

  PATH may be either a SKILL.md file or a skill directory (defaults to
  the current working directory). If PATH is a directory, the script
  looks for SKILL.md inside it.

EXAMPLES
  scripts/validate_frontmatter.py
  scripts/validate_frontmatter.py ./my-skill/
  scripts/validate_frontmatter.py ./my-skill/SKILL.md --format json

EXIT CODES
  0   All checks passed.
  1   Validation failure (one or more frontmatter constraints violated).
  2   Could not read SKILL.md or parse its YAML frontmatter.

DEPENDENCIES
  This script uses PEP 723 inline metadata. With `uv` installed
  (https://docs.astral.sh/uv/), running it via the shebang or
  `uv run scripts/validate_frontmatter.py` resolves PyYAML
  automatically into an isolated environment. With `pipx`,
  `pipx run scripts/validate_frontmatter.py` works equivalently.
  If neither is available, install PyYAML manually:
  `pip install --user pyyaml`.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.stderr.write(
        "ERROR: PyYAML is required.\n"
        "  Run via `uv run scripts/validate_frontmatter.py` (recommended)\n"
        "  or `pipx run scripts/validate_frontmatter.py`\n"
        "  or install manually: `pip install --user pyyaml`\n"
    )
    sys.exit(2)


SPEC_URL = "https://agentskills.io/specification"

# Constraints (synced with spec; see references/spec-check.md to verify drift).
NAME_PATTERN = re.compile(r"^[a-z]+(-[a-z]+)*$")
NAME_MAX_LEN = 64
DESCRIPTION_MAX_LEN = 1024
COMPATIBILITY_MAX_LEN = 500

KNOWN_FIELDS = frozenset(
    {"name", "description", "license", "compatibility", "metadata", "allowed-tools"}
)


# ----------------------------- helpers ---------------------------------


def locate_skill_md(path_arg: str) -> Path | None:
    """Resolve PATH to a SKILL.md file. Returns None if not found."""
    p = Path(path_arg).resolve()
    if p.is_dir():
        candidate = p / "SKILL.md"
        return candidate if candidate.exists() else None
    if p.is_file():
        return p
    return None


def parse_frontmatter(skill_md: Path) -> dict:
    """Extract and parse the YAML frontmatter from a SKILL.md file."""
    text = skill_md.read_text(encoding="utf-8")
    parts = text.split("---", 2)
    if len(parts) < 3:
        raise ValueError(
            "No YAML frontmatter found (expected leading '---' / '---' delimiters)"
        )
    fm = yaml.safe_load(parts[1])
    if not isinstance(fm, dict):
        raise ValueError(
            f"Frontmatter parsed as {type(fm).__name__}; expected a YAML mapping"
        )
    return fm


# --------------------------- field checks ------------------------------
# Each check returns (passed: bool, message: str). The message should be
# specific enough that an agent or developer can act on it without
# consulting the spec.


def check_name(fm: dict, parent_dir_name: str) -> tuple[bool, str]:
    name = fm.get("name")
    if not name:
        return False, "name: missing (required field)"
    if not isinstance(name, str):
        return False, f"name: must be a string, got {type(name).__name__}"
    if len(name) > NAME_MAX_LEN:
        return False, f"name: {len(name)} chars > {NAME_MAX_LEN} char limit"
    if not NAME_PATTERN.match(name):
        return False, (
            f"name: {name!r} violates the allowed-character rule. "
            "Must be lowercase ASCII a-z and single hyphens only — "
            "no uppercase, no underscores, no leading/trailing hyphens, "
            "no consecutive hyphens (--)."
        )
    if name != parent_dir_name:
        return False, (
            f"name: {name!r} does not match parent directory name {parent_dir_name!r}. "
            "The Agent Skills spec requires these to be identical at install time."
        )
    return True, f"name: OK ({name!r}; matches parent directory)"


def check_description(fm: dict) -> tuple[bool, str]:
    desc = fm.get("description")
    if not desc:
        return False, "description: missing (required field)"
    if not isinstance(desc, str):
        return False, f"description: must be a string, got {type(desc).__name__}"
    n = len(desc)
    if n > DESCRIPTION_MAX_LEN:
        return False, (
            f"description: {n} chars > {DESCRIPTION_MAX_LEN} char limit. "
            "Installer rejects with: "
            "'field description in SKILL.md must be at most 1024 characters'. "
            "Trim trigger lists, drop parenthetical methodology mentions, "
            "or move details to the SKILL.md body."
        )
    headroom = DESCRIPTION_MAX_LEN - n
    return True, f"description: OK ({n} chars, {headroom} headroom)"


def check_compatibility(fm: dict) -> tuple[bool, str]:
    compat = fm.get("compatibility")
    if compat is None:
        return True, "compatibility: not set (optional)"
    if not isinstance(compat, str):
        return False, f"compatibility: must be a string, got {type(compat).__name__}"
    n = len(compat)
    if n > COMPATIBILITY_MAX_LEN:
        return False, f"compatibility: {n} chars > {COMPATIBILITY_MAX_LEN} char limit"
    return True, f"compatibility: OK ({n} chars)"


def check_metadata(fm: dict) -> tuple[bool, str]:
    md = fm.get("metadata")
    if md is None:
        return True, "metadata: not set (optional)"
    if not isinstance(md, dict):
        return False, f"metadata: must be a YAML mapping, got {type(md).__name__}"
    return True, f"metadata: OK ({len(md)} keys)"


def check_allowed_tools(fm: dict) -> tuple[bool, str]:
    at = fm.get("allowed-tools")
    if at is None:
        return True, "allowed-tools: not set (optional)"
    if not isinstance(at, str):
        return False, f"allowed-tools: must be a string, got {type(at).__name__}"
    return True, "allowed-tools: OK (experimental — support varies by client)"


def check_unknown_fields(fm: dict) -> tuple[bool, str]:
    unknown = sorted(set(fm.keys()) - KNOWN_FIELDS)
    if not unknown:
        return True, "unknown fields: none"
    return True, (
        f"unknown fields: {unknown} — these may be valid additions to a newer spec. "
        f"Verify at {SPEC_URL}."
    )


# --------------------------- orchestration -----------------------------


def run_all_checks(fm: dict, parent_dir_name: str) -> list[dict]:
    """Run all frontmatter checks and return a list of result dicts."""
    return [
        {"field": "name",          "passed": (r := check_name(fm, parent_dir_name))[0],          "message": r[1]},
        {"field": "description",   "passed": (r := check_description(fm))[0],                    "message": r[1]},
        {"field": "compatibility", "passed": (r := check_compatibility(fm))[0],                  "message": r[1]},
        {"field": "metadata",      "passed": (r := check_metadata(fm))[0],                       "message": r[1]},
        {"field": "allowed-tools", "passed": (r := check_allowed_tools(fm))[0],                  "message": r[1]},
        {"field": "schema",        "passed": (r := check_unknown_fields(fm))[0],                 "message": r[1]},
    ]


def render_text(results: list[dict], any_failed: bool) -> None:
    """Render results to stdout in human-readable form."""
    for r in results:
        mark = "PASS" if r["passed"] else "FAIL"
        print(f"  [{mark}] {r['message']}")
    print()
    if any_failed:
        print(
            f"FAILED — one or more frontmatter constraints violated. "
            f"See {SPEC_URL} for the authoritative rules."
        )
    else:
        print("PASSED — all frontmatter constraints met.")


def render_json(skill_md_path: Path, results: list[dict], any_failed: bool) -> None:
    """Render results to stdout as a single JSON document."""
    payload = {
        "skill_md": str(skill_md_path),
        "spec": SPEC_URL,
        "all_passed": not any_failed,
        "results": results,
    }
    print(json.dumps(payload, indent=2))


# ------------------------------ main -----------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(
        description=f"Validate a SKILL.md frontmatter against {SPEC_URL}.",
        epilog="Exit codes: 0 = all pass, 1 = validation failure, 2 = parse error.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "path",
        nargs="?",
        default=".",
        help="Path to SKILL.md or to a skill directory (default: current dir).",
    )
    parser.add_argument(
        "--format",
        choices=("text", "json"),
        default="text",
        help="Output format (default: text).",
    )
    args = parser.parse_args()

    skill_md_path = locate_skill_md(args.path)
    if not skill_md_path:
        sys.stderr.write(f"ERROR: No SKILL.md found at {args.path!r}\n")
        return 2

    try:
        fm = parse_frontmatter(skill_md_path)
    except Exception as e:
        sys.stderr.write(f"ERROR: Could not parse {skill_md_path}: {e}\n")
        return 2

    parent_dir_name = skill_md_path.parent.name
    results = run_all_checks(fm, parent_dir_name)
    any_failed = any(not r["passed"] for r in results)

    if args.format == "json":
        render_json(skill_md_path, results, any_failed)
    else:
        render_text(results, any_failed)

    return 1 if any_failed else 0


if __name__ == "__main__":
    sys.exit(main())
