#!/usr/bin/env python3
"""PII scrub and audit for files about to be shared externally.

Applies user-provided context-token substitutions plus a baseline library of
PII regex patterns from patterns.json. Audits the result; exits non-zero if
any pattern still matches after substitution.

The skill that owns this script lives at ~/.claude/skills/pii-scrub/.
See SKILL.md for the full procedure and gotchas.

Usage:
    scrub.py --files file1.txt file2.log \\
             --sub alice=\\<user\\> --sub lab-host=\\<hostname\\>

    scrub.py --files file.log --audit-only

    scrub.py --files file.log --sub-regex '\\bshorttoken\\b=<redacted>'

Tested on Python 3.8+. No third-party dependencies.
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path


def is_textual(path: Path, sample_size: int = 8192) -> bool:
    """Heuristic: if first 8KB has >1% null bytes, treat as binary."""
    if not path.exists() or path.stat().st_size == 0:
        return False
    try:
        with path.open("rb") as fh:
            sample = fh.read(sample_size)
    except OSError:
        return False
    if not sample:
        return False
    null_count = sample.count(b"\x00")
    return (null_count / len(sample)) < 0.01


def parse_kv(items, label, split_on_last=False):
    """Parse KEY=VALUE strings into a dict.

    split_on_last=False (default, used for --sub literal subs): split at the
    FIRST '='. The key is a literal token (username, hostname, etc.) and almost
    never contains '='; the replacement value may (e.g. --sub 'myhost=server=01').

    split_on_last=True (used for --sub-regex): split at the LAST '='. The regex
    pattern may contain '=' (lookaheads, literals) so splitting first would corrupt
    the pattern; the replacement is typically a short placeholder that won't contain '='.
    """
    out = {}
    if not items:
        return out
    for item in items:
        if "=" not in item:
            sys.stderr.write(f"warning: --{label} entry missing '=': {item!r}\n")
            continue
        if split_on_last:
            key, value = item.rsplit("=", 1)
        else:
            key, value = item.split("=", 1)
        out[key] = value
    return out


_DOLLAR_BACKREF = re.compile(r"\$(?:\$|(\d))")


def _translate_replacement(replacement: str) -> str:
    """Translate PowerShell-style $N backreferences to Python's \\N,
    and PowerShell-style $$ escape to literal $.

    Used for REGEX substitutions (--sub-regex and patterns.json), where the
    pattern can legitimately have capture groups that $N should reference.

    patterns.json uses PowerShell's $1, $2, ... convention because it's the
    primary engine. Python's re.sub uses \\1, \\2, ... so we translate here
    so the same patterns.json works for both engines. PowerShell's $$ escape
    for a literal $ is honored too so the cross-engine workaround in SKILL.md
    actually works on the Python side.
    """
    def _sub(m):
        if m.group(1) is None:  # $$ matched -> emit literal $
            return '$'
        return '\\' + m.group(1)
    return _DOLLAR_BACKREF.sub(_sub, replacement)


def _translate_replacement_for_literal(replacement: str) -> str:
    """Translate replacement strings for LITERAL-key substitutions.

    Literal-key substitutions use re.escape(key) as the regex, which has no
    capture groups by construction. PowerShell's -replace behavior for such
    replacements (verified empirically against pwsh 7.5.5):
        $$  -> literal $
        $0  -> whole match (always defined)
        $N  -> preserved as literal $N (because group N doesn't exist)
    Translate to keep Python's re.sub aligned:
        $$  -> literal $       (PS escape -> our escape)
        $0  -> \\g<0>          (Python's whole-match syntax in replacement)
        $N  -> leave alone     (Python re.sub treats $ as non-metachar so $N
                                passes through as literal, matching PS)
    Without this translation, Python's re.sub would raise re.error on $N
    references because re.sub interprets neither $$ nor $0 the way PS does.
    """
    def _sub(m):
        if m.group(1) is None:        # $$ matched
            return '$'
        if m.group(1) == '0':         # $0 -> whole match
            return '\\g<0>'
        return m.group(0)             # $N (N>=1) -> literal $N
    return _DOLLAR_BACKREF.sub(_sub, replacement)


def apply_substitutions(content, literal_subs, regex_subs):
    for key, replacement in literal_subs.items():
        if not key:
            sys.stderr.write("warning: skipping empty literal substitution key\n")
            continue
        pattern = re.compile(re.escape(key), re.IGNORECASE)
        # Literal-key patterns have no capture groups by construction. Use the
        # literal-sub translator so $N references resolve to empty (matching
        # PowerShell's silent-empty behavior) instead of crashing on
        # 'invalid group reference N'. See SKILL.md gotcha section.
        content = pattern.sub(_translate_replacement_for_literal(replacement), content)
    for key, replacement in regex_subs.items():
        try:
            content = re.sub(key, _translate_replacement(replacement), content)
        except re.error as exc:
            sys.stderr.write(f"warning: bad --sub-regex pattern {key!r}: {exc}\n")
    return content


def audit_file(path: Path, patterns, literal_subs, regex_subs, extra_audit):
    hits = []
    if not is_textual(path):
        return hits
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return hits
    for entry in patterns:
        matches = list(re.finditer(entry["pattern"], text))
        if matches:
            hits.append(
                {
                    "file": str(path),
                    "pattern": entry["name"],
                    "count": len(matches),
                    "sample": matches[0].group(0),
                }
            )
    for key in literal_subs:
        if not key:
            continue
        matches = list(re.finditer(re.escape(key), text, re.IGNORECASE))
        if matches:
            hits.append(
                {
                    "file": str(path),
                    "pattern": f"context-literal: {key}",
                    "count": len(matches),
                    "sample": matches[0].group(0),
                }
            )
    for key in regex_subs:
        try:
            matches = list(re.finditer(key, text))
        except re.error:
            continue
        if matches:
            hits.append(
                {
                    "file": str(path),
                    "pattern": f"context-regex: {key}",
                    "count": len(matches),
                    "sample": matches[0].group(0),
                }
            )
    for entry in extra_audit:
        matches = list(re.finditer(entry["pattern"], text))
        if matches:
            hits.append(
                {
                    "file": str(path),
                    "pattern": f"extra: {entry['name']}",
                    "count": len(matches),
                    "sample": matches[0].group(0),
                }
            )
    return hits


def main():
    parser = argparse.ArgumentParser(
        description="Scrub PII from files for external sharing.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--files",
        nargs="+",
        required=True,
        help="Paths of files to scrub.",
    )
    parser.add_argument(
        "--sub",
        action="append",
        metavar="KEY=VALUE",
        help="Literal context substitution (case-insensitive). Repeatable.",
    )
    parser.add_argument(
        "--sub-regex",
        action="append",
        metavar="PATTERN=VALUE",
        help="Regex context substitution. Repeatable. Use for word boundaries.",
    )
    parser.add_argument(
        "--patterns",
        default=None,
        help="Path to patterns.json. Defaults to the file next to this script.",
    )
    parser.add_argument(
        "--audit-only",
        action="store_true",
        help="Skip substitution. Audit pass only.",
    )
    args = parser.parse_args()

    patterns_path = (
        Path(args.patterns)
        if args.patterns
        else Path(__file__).resolve().parent / "patterns.json"
    )
    if not patterns_path.exists():
        sys.stderr.write(f"error: patterns.json not found at {patterns_path}\n")
        return 2

    with patterns_path.open("r", encoding="utf-8") as fh:
        config = json.load(fh)
    baseline_patterns = config.get("baseline", [])
    audit_only_patterns = config.get("audit_only", [])

    literal_subs = parse_kv(args.sub, "sub", split_on_last=False)
    regex_subs = parse_kv(args.sub_regex, "sub-regex", split_on_last=True)
    files = [Path(p) for p in args.files]

    # === Substitution pass ===
    if not args.audit_only:
        for path in files:
            if not path.exists():
                sys.stderr.write(f"warning: skipping (not found): {path}\n")
                continue
            if path.stat().st_size == 0:
                sys.stderr.write(f"warning: skipping (empty): {path}\n")
                continue
            if not is_textual(path):
                sys.stderr.write(f"warning: skipping (binary): {path}\n")
                continue
            try:
                original = path.read_text(encoding="utf-8")
            except UnicodeDecodeError:
                sys.stderr.write(f"warning: skipping (non-utf8): {path}\n")
                continue
            if not original:
                continue
            new = apply_substitutions(original, literal_subs, regex_subs)
            for entry in baseline_patterns:
                new = re.sub(entry["pattern"], _translate_replacement(entry["replacement"]), new)
            if new != original:
                path.write_text(new, encoding="utf-8", newline="")
                print(f"scrubbed: {path}")
            else:
                print(f"unchanged: {path}")

    # === Audit pass ===
    print("\n=== Audit pass ===")
    all_hits = []
    skipped = []  # files we couldn't audit (binary / missing / etc.)
    audit_patterns = baseline_patterns + audit_only_patterns
    for path in files:
        if not path.exists():
            skipped.append((path, "not found"))
            continue
        if path.stat().st_size == 0:
            skipped.append((path, "empty file"))
            continue
        if not is_textual(path):
            # Common case on Windows: PowerShell's default Out-File / > / Export-*
            # cmdlets emit UTF-16 LE, which is_textual classifies as binary.
            # Captured PS session logs land here.
            skipped.append((path, "binary or non-UTF-8 (UTF-16 / encoded)"))
            continue
        all_hits.extend(
            audit_file(path, audit_patterns, literal_subs, regex_subs, [])
        )

    audited_count = len(files) - len(skipped)
    if not all_hits and not skipped:
        pattern_count = (
            len(baseline_patterns)
            + len(audit_only_patterns)
            + len(literal_subs)
            + len(regex_subs)
        )
        print(
            f"VERDICT: CLEAN. Zero hits across {pattern_count} patterns "
            f"in {len(files)} file(s)."
        )
    elif not all_hits and skipped:
        print(
            f"VERDICT: AUDITED {audited_count} of {len(files)} files; "
            f"{len(skipped)} skipped (could not safely scan as text). "
            f"Cannot certify CLEAN."
        )
        for path, reason in skipped:
            print(f"  skipped: {path} ({reason})")
        print(
            "\nIf any skipped file may contain PII, either re-encode it as UTF-8 "
            "first or scrub it by hand. The audit cannot inspect files it cannot "
            "decode as text."
        )
        return 1
    else:
        print(f"VERDICT: {len(all_hits)} hit(s) remaining. Review:")
        for hit in all_hits:
            sample = hit["sample"][:80].replace("\n", " ")
            print(
                f"  {hit['file']} | {hit['pattern']} | "
                f"count={hit['count']} | sample={sample!r}"
            )
        if skipped:
            print(f"\nALSO: {len(skipped)} file(s) skipped (could not safely scan as text):")
            for path, reason in skipped:
                print(f"  skipped: {path} ({reason})")
        print(
            "\nNOTE: audit_only patterns (e.g., private-key-block, "
            "long-base64-blob) are flagged for review, not auto-substituted."
        )
        return 1

    # === Manual review prompt ===
    textual = [p for p in files if is_textual(p)]
    if textual:
        biggest = sorted(textual, key=lambda p: p.stat().st_size, reverse=True)[:2]
        print("\nMANUAL REVIEW recommended for the largest output files:")
        for path in biggest:
            print(f"  - {path} ({path.stat().st_size} bytes)")
        print(
            "\nPattern matching catches structured PII. It does NOT catch "
            "identifying free-form text."
        )
        print("Skim these before sharing externally.")

    return 0


if __name__ == "__main__":
    sys.exit(main())
