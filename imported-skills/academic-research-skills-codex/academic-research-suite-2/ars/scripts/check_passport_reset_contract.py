#!/usr/bin/env python3
"""Enforce the ARS v3.6.3 passport-reset-boundary co-location contract.

Contract: any text file that mentions the env-flag token `ARS_PASSPORT_RESET`
MUST also contain a reference to the protocol-doc stem `passport_as_reset_boundary`
so a reader encountering the flag can trace it back to the authoritative spec at
`academic-pipeline/references/passport_as_reset_boundary.md`.

Also enforces: `pending_decision.options[]` must have unique `value` fields within
each options array in YAML fenced blocks found in markdown files under the repo root.

Exemptions:
  - The protocol doc itself — identified by filename + parent-dir match
    (`references/passport_as_reset_boundary.md`). More robust than path-suffix
    match against `--root`: works whether the lint is invoked from repo root
    or from a sub-tree.
  - Binary / non-UTF-8 files — skipped silently to avoid false positives from
    embedded bytes that happen to spell the flag token.

Exit code: 0 clean, 1 on any violation (list of offending files printed to
stderr). CLI: `--root <path>` (default `.`).
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

import yaml

FLAG_TOKEN = "ARS_PASSPORT_RESET"
PROTOCOL_TOKEN = "passport_as_reset_boundary"
PROTOCOL_FILENAME = "passport_as_reset_boundary.md"
PROTOCOL_PARENT_DIRNAME = "references"

# Directories we never scan: VCS, caches, build output, local tooling scratch.
# `.context` and `.codex-rounds` are hand-off / codex-review log scratch
# (gitignored per repo .gitignore); files there routinely quote the
# ARS_PASSPORT_RESET token from prior work without owing the protocol-doc
# co-location.
SKIP_DIRS = {
    ".git",
    "node_modules",
    "__pycache__",
    ".venv",
    "dist",
    "build",
    ".gstack",
    ".context",
    ".codex-rounds",
}


def _is_under_skip_dir(path: Path, root: Path) -> bool:
    """True if any path component between root and file is a skip-listed dir."""
    try:
        rel = path.relative_to(root)
    except ValueError:
        return False
    return any(part in SKIP_DIRS for part in rel.parts)


def _read_text_or_none(path: Path) -> str | None:
    """Return file contents as UTF-8 text, or None if unreadable / non-text."""
    try:
        return path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError):
        return None


def _is_protocol_doc(path: Path) -> bool:
    """True if `path` IS the authoritative protocol reference doc."""
    return path.name == PROTOCOL_FILENAME and path.parent.name == PROTOCOL_PARENT_DIRNAME


def scan(root: Path) -> list[str]:
    """Walk `root` and return list of violation messages (empty if clean)."""
    violations: list[str] = []
    for path in sorted(root.rglob("*")):
        if not path.is_file():
            continue
        if _is_under_skip_dir(path, root):
            continue

        content = _read_text_or_none(path)
        if content is None or FLAG_TOKEN not in content:
            continue

        if _is_protocol_doc(path):
            # Protocol doc is exempt — it IS the reference.
            continue

        if PROTOCOL_TOKEN not in content:
            rel = path.relative_to(root).as_posix()
            violations.append(
                f"{rel}: mentions {FLAG_TOKEN} but does not reference "
                f"{PROTOCOL_TOKEN} (co-location required by ARS v3.6.3 contract)"
            )

    return violations


# Regex to extract fenced YAML blocks from markdown files.
# Accepts `yaml`/`yml`, optional trailing whitespace after the fence,
# and CRLF line endings (Windows-authored docs).
_FENCED_YAML_RE = re.compile(
    r"```ya?ml[ \t]*\r?\n(.*?)\r?\n```",
    re.DOTALL,
)


def scan_duplicate_option_values(root: Path) -> list[str]:
    """Walk `root` for markdown files; find YAML fenced blocks with pending_decision;
    check each options array for duplicate `value` fields.

    Returns a list of violation messages (empty if clean).
    """
    violations: list[str] = []
    for path in sorted(root.rglob("*.md")):
        if not path.is_file():
            continue
        if _is_under_skip_dir(path, root):
            continue

        content = _read_text_or_none(path)
        if content is None or "pending_decision" not in content:
            continue

        rel = path.relative_to(root).as_posix()
        for match in _FENCED_YAML_RE.finditer(content):
            block_text = match.group(1)
            if "pending_decision" not in block_text:
                continue

            try:
                data = yaml.safe_load(block_text)
            except yaml.YAMLError:
                # Malformed YAML block: skip silently. Other lints cover schema validity.
                continue

            if not isinstance(data, dict):
                continue

            entries = data.get("reset_boundary", [])
            if not isinstance(entries, list):
                continue

            for entry in entries:
                if not isinstance(entry, dict):
                    continue
                pd = entry.get("pending_decision")
                if not isinstance(pd, dict):
                    continue
                options = pd.get("options", [])
                if not isinstance(options, list):
                    continue

                seen: set[str] = set()
                duplicates: set[str] = set()
                for opt in options:
                    if not isinstance(opt, dict):
                        continue
                    val = opt.get("value")
                    if val is None:
                        continue
                    if val in seen:
                        duplicates.add(str(val))
                    seen.add(str(val))

                entry_hash = entry.get("hash", "<unknown>")
                for dup in sorted(duplicates):
                    violations.append(
                        f"{rel}: pending_decision.options[] in entry "
                        f"hash={entry_hash} contains duplicate value "
                        f"'{dup}'. Values must be unique within each options "
                        f"array (ARS v3.6.3 contract)."
                    )

    return violations


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Enforce the ARS v3.6.3 passport-reset co-location contract: every "
            f"file mentioning {FLAG_TOKEN} must also reference {PROTOCOL_TOKEN}."
        )
    )
    parser.add_argument(
        "--root",
        default=".",
        help="Repo root to scan (default: current directory).",
    )
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    if not root.is_dir():
        print(f"error: --root {args.root} is not a directory", file=sys.stderr)
        return 2

    violations = scan(root)
    violations += scan_duplicate_option_values(root)
    if violations:
        print("Passport reset contract lint FAILED:", file=sys.stderr)
        for v in violations:
            print(f"  - {v}", file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
