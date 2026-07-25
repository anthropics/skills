"""ARS /ars-mark-read + /ars-unmark-read CLI implementation.

Implements v3.6.8 spec §3.6 + Step 7 (round-2 R2-002, round-5 R5-003 amends).

The command writes a peer file `<passport-stem>_human_read_log.yaml` next to
the active passport. The peer file is the canonical user-owned signal source;
the literature_corpus[] schema is adapter-owned and MUST NOT be mutated to
carry `human_read_source` (v3.6.8 §3.1 firm rule 3).

Usage:
    python3 scripts/ars_mark_read.py <citation_key>... --passport-path <path>
    python3 scripts/ars_mark_read.py <citation_key>... --passport-path <path> --unmark

Behavior summary:
- 4 fail-fast modes (no passport / not found / parent unreadable / unwritable)
  emit canonical `[ARS-MARK-READ ERROR: ...]` and exit non-zero.
- Invalid citation_key (not in active corpus) is a hard error per §3.6 firm
  rule 2. Batch with any invalid key is rejected whole (no partial writes).
- Append-only YAML write per §3.6 firm rule 3. /ars-unmark-read writes
  `rescinded_at` to the matching entry, never deletes.
- First-time write creates the file with the YAML schema header. Not a
  fail-fast condition.
"""
from __future__ import annotations

import argparse
import os
import sys
import uuid
from datetime import datetime, timezone
from pathlib import Path

import yaml

ERR_PREFIX = "[ARS-MARK-READ ERROR:"


def _err(msg: str) -> str:
    return f"{ERR_PREFIX} {msg}]"


def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _read_log_path(passport_path: Path) -> Path:
    return passport_path.parent / f"{passport_path.stem}_human_read_log.yaml"


def _validate_passport_environment(passport_path: Path | None) -> tuple[Path, Path]:
    """Run the 4 fail-fast checks per §3.6 R5-003 amend.

    Returns (passport_path, read_log_path) if all checks pass; raises
    SystemExit with the canonical error message otherwise.
    """
    if passport_path is None:
        print(
            _err(
                "no active passport path; run a session with passport "
                "handoff first or pass --passport-path explicitly"
            ),
            file=sys.stderr,
        )
        raise SystemExit(2)

    parent = passport_path.parent
    # Check parent R_OK BEFORE passport.exists() — pathlib's stat() raises
    # PermissionError on an unreadable parent, which would mask the canonical
    # error we want to emit.
    if not os.access(parent, os.R_OK):
        print(
            _err(f"passport parent directory {parent} unreadable"),
            file=sys.stderr,
        )
        raise SystemExit(2)

    if not passport_path.exists():
        print(_err(f"passport file not found at {passport_path}"), file=sys.stderr)
        raise SystemExit(2)

    if not os.access(parent, os.W_OK):
        log_path = _read_log_path(passport_path)
        print(
            _err(
                f"read-log path target is unwritable at {log_path}; "
                "parent directory not writable"
            ),
            file=sys.stderr,
        )
        raise SystemExit(2)

    log_path = _read_log_path(passport_path)
    if log_path.exists() and not os.access(log_path, os.W_OK):
        print(
            _err(
                f"read-log path target is unwritable at {log_path}; "
                "existing file not writable"
            ),
            file=sys.stderr,
        )
        raise SystemExit(2)

    return passport_path, log_path


def _load_corpus_keys(passport_path: Path) -> set[str]:
    with passport_path.open(encoding="utf-8") as f:
        passport = yaml.safe_load(f) or {}
    corpus = passport.get("literature_corpus", []) or []
    return {entry["citation_key"] for entry in corpus if "citation_key" in entry}


def _load_log(log_path: Path) -> dict:
    if not log_path.exists():
        return {
            "session_id": str(uuid.uuid4()),
            "created_at": _now_iso(),
            "human_read": [],
        }
    with log_path.open(encoding="utf-8") as f:
        data = yaml.safe_load(f) or {}
    data.setdefault("human_read", [])
    return data


def _save_log(log_path: Path, data: dict) -> None:
    with log_path.open("w", encoding="utf-8") as f:
        yaml.safe_dump(data, f, sort_keys=False, allow_unicode=True)


def _mark(log: dict, citation_key: str) -> None:
    log["human_read"].append(
        {"citation_key": citation_key, "marked_at": _now_iso()}
    )


def _unmark(log: dict, citation_key: str) -> bool:
    """Append `rescinded_at` to the most recent matching entry without a
    prior rescind. Returns True if found, False otherwise."""
    for entry in reversed(log["human_read"]):
        if entry["citation_key"] == citation_key and "rescinded_at" not in entry:
            entry["rescinded_at"] = _now_iso()
            return True
    return False


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="ARS /ars-mark-read peer-file writer (v3.6.8 §3.6)."
    )
    parser.add_argument(
        "citation_keys",
        nargs="+",
        help="Citation keys to mark (or unmark with --unmark).",
    )
    parser.add_argument(
        "--passport-path",
        type=Path,
        default=None,
        help="Active Material Passport JSON path.",
    )
    parser.add_argument(
        "--unmark",
        action="store_true",
        help="Rescind prior marks (write rescinded_at instead of marked_at).",
    )
    args = parser.parse_args(argv)

    passport_path, log_path = _validate_passport_environment(args.passport_path)
    corpus_keys = _load_corpus_keys(passport_path)

    # Validate all keys up-front; refuse to write on any invalid key
    # (§3.6 firm rule 2, batch-level all-or-nothing).
    invalid = [k for k in args.citation_keys if k not in corpus_keys]
    if invalid:
        for k in invalid:
            print(
                _err(f"citation_key '{k}' not in literature_corpus[]"),
                file=sys.stderr,
            )
        return 2

    log = _load_log(log_path)

    if args.unmark:
        not_found = [
            k for k in args.citation_keys if not _unmark(log, k)
        ]
        if not_found:
            for k in not_found:
                print(
                    _err(
                        f"citation_key '{k}' has no active mark to rescind"
                    ),
                    file=sys.stderr,
                )
            return 2
    else:
        for k in args.citation_keys:
            _mark(log, k)

    _save_log(log_path, log)
    return 0


if __name__ == "__main__":
    sys.exit(main())
