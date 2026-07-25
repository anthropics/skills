#!/usr/bin/env python3
"""Lint: version labels stay aligned across .claude/CLAUDE.md, SKILL.md frontmatter, and CHANGELOG.md.

Invariants enforced:
  1. Every skill listed in .claude/CLAUDE.md Skills Overview table has a version
     equal to its own SKILL.md metadata.version.
  2. .claude/CLAUDE.md "**Suite version**: X.Y.Z" equals the most recent
     "## [X.Y.Z]" entry in CHANGELOG.md.
  3. academic-pipeline version in the table equals the suite version (pipeline
     = orchestrator, by convention tracks the suite release).
  4. The plugin manifests (.claude-plugin/plugin.json "version" and
     .claude-plugin/marketplace.json plugins[].version) equal the suite version.
     These are the repo's OUTWARD-FACING package metadata — a user updating the
     plugin sees them — and were the one surface a v3.10.0 release-doc pass missed
     because no lint covered them (marketplace had silently sat at 3.7.0).
  5. The README.md shields.io version badge (`badge/version-vX.Y.Z`) equals the
     suite version — the most outward-facing surface of all.
  6. No docs/*.md cites a `vX.Y.Z` ABOVE the suite version (a forward/unknown
     reference misleads readers). Equal-to-suite is allowed.
  7. Every version-bearing H2 heading in docs/<name>.md has a matching
     version-bearing H2 (same version) in docs/<name>.zh-TW.md and vice versa.
     Plain headings may differ — only version TAGS must stay in lockstep.
  8. The plugin.json description's "N-agent" claim (when present) equals the
     number of unique *_agent.md files in the tree (#414: the advertised
     number had silently drifted from the tree). The plugin-root agents/
     mirror dir is excluded from the count — real byte-identical copies of
     deep-research agents since #413 (symlinks before that), pinned as pure
     aliases by check_agents_mirror_sync.py, never a source of new agents.
  9. The latest CHANGELOG entry's body is >= 100 characters (#487) — a bare
     heading or one-line stub is not release notes. Only the LATEST entry is
     gated; historical entries may be terse.
 10. .claude/CLAUDE.md "Last Updated" lies within ±7 days of the latest
     CHANGELOG entry's date (#487). The CHANGELOG date is the baseline (not
     "today") so re-running the lint later cannot flip the result.
 11. The newest "## vX.Y… Key Additions" heading in .claude/CLAUDE.md matches
     the suite version (#487), compared at the heading's own precision —
     `## v3.14 Key Additions` matches suite 3.14.0.

Tag gate (#487): `--tag <ref>` additionally requires the given git tag
(leading `v` optional) to equal the suite version — the one comparison
nothing else performs at tag time. Wired via tag-version-match.yml.

Runs from repo root by default; `--path` lets tests point at a fake tree.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from datetime import date
from pathlib import Path

from _skill_lint import parse_frontmatter, FrontmatterError


# Broad token captures: anything that looks like an identifier inside the
# expected position. The strict validator below then decides whether the raw
# token is a canonical semver. Using the regex as a filter (the pre-#169
# pattern) silently dropped invalid tokens and hid the very drift this lint
# is meant to surface; see dual-track review on PR for that class of bug.
TABLE_TOKEN_RE = re.compile(
    r"^\|\s*`([a-z0-9-]+)`\s+v([A-Za-z0-9.\-_+]+)\s*\|", re.MULTILINE
)
SUITE_TOKEN_RE = re.compile(
    r"^\s*-\s*\*\*Suite version\*\*:\s*([A-Za-z0-9.\-_+]+)", re.MULTILINE
)
CHANGELOG_TOKEN_RE = re.compile(r"^##\s*\[([A-Za-z0-9.\-_+]+)\]", re.MULTILINE)
SEMVER_STRICT_RE = re.compile(r"^\d+(?:\.\d+){2,3}$")  # exactly 3 or 4 segments (N.N.N or N.N.N.N)

# Invariant 5: shields.io version badge label, e.g. `badge/version-v3.11.1-blue`.
# `_VSEG` = 3-or-4 numeric segments. The trailing `(?!\.?\d)` stops a 5th
# segment (`3.11.1.2.3` would otherwise yield `3.11.1.2`); the label's own
# `-<color>` separator already bounds the token on the right, so no broader
# suffix lookahead is needed here. Keyed off the label, not the release URL.
_VSEG = r"(\d+(?:\.\d+){2,3})"
README_BADGE_RE = re.compile(r"badge/version-v" + _VSEG + r"(?!\.?\d)", re.IGNORECASE)
# Invariant 6 only: a CANONICAL `vX.Y.Z(.W)` token in docs prose. The leading
# `(?<![\w.])` blocks mid-identifier matches; the trailing `(?![\d.\-+A-Za-z])`
# drops prerelease/build/5-segment tokens ENTIRELY (`v3.12.0-alpha`,
# `v3.11.1.2.3`) rather than partial-matching them (review finding). `_VSEG` is
# 3-or-4 segments, so a 2-segment `v3.10` never matches and is silently
# ignored (inv 6 gates only on full release tokens; a partial like `v3.10`
# is not a version this lint adjudicates). Invariant 7 uses H2_VERSION_RE.
DOCS_VERSION_RE = re.compile(r"(?<![\w.])v" + _VSEG + r"(?![\d.\-+A-Za-z])")
# Invariant 7: version tag inside an H2 heading, e.g. `## Corpus (v3.6.4+)`.
# Same canonical-token shape, but a trailing `+` IS allowed (the repo's
# "vX.Y.Z and later" heading convention, e.g. `(v3.6.4+)`); only `-`/letters/
# extra `.N` segments disqualify.
H2_RE = re.compile(r"^##\s+(.*?)\s*$", re.MULTILINE)
H2_VERSION_RE = re.compile(r"(?<![\w.])v" + _VSEG + r"(?![\d.\-A-Za-z])")

NON_VERSION_CHANGELOG_TOKENS = frozenset({"Unreleased"})

# Invariant 8: the outward-facing agent-count claim, e.g. "38-agent ensemble".
AGENT_CLAIM_RE = re.compile(r"(\d+)-agent")

# Invariant 9: minimum body length (chars, after strip) for the latest entry.
CHANGELOG_BODY_MIN_CHARS = 100
# Invariant 10: the release date on a `## [X.Y.Z] - YYYY-MM-DD` heading (ARS
# headings may append an em-dash summary after the date) and the
# `- **Last Updated**: YYYY-MM-DD` line in .claude/CLAUDE.md. The trailing
# `(?!\d)` blocks prefix-capturing a longer run (`2026-04-222` must not read
# as `2026-04-22`, codex re-review P3); the day field then fails the strict
# ISO gate downstream.
CHANGELOG_DATE_RE = re.compile(r"\]\s*-\s*(\d{4}-\d{2}-\d{2})(?!\d)")
LAST_UPDATED_RE = re.compile(
    r"^\s*-\s*\*\*Last Updated\*\*:\s*(\S+)", re.MULTILINE
)
LAST_UPDATED_MAX_DAYS = 7
# Invariant 11: a version-tagged Key Additions H2, e.g. `## v3.14 Key
# Additions (...)`. 2-4 segments — headings cite major.minor or a full patch.
KEY_ADDITIONS_RE = re.compile(
    r"^##\s+v(\d+(?:\.\d+){1,3})\s+Key Additions", re.MULTILINE
)
# A release-entry heading (`## [X.Y.Z]`). Applied per-line by _next_entry_offset
# (fence-aware), so no MULTILINE — the latest entry's body ends at the next
# such heading OUTSIDE a code fence, never at a `## ` inside one (codex P2-1).
# `[Unreleased]` never appears below the latest release entry, so keying on the
# `[` bracket is sufficient.
NEXT_ENTRY_RE = re.compile(r"##\s+\[")
# Strict YYYY-MM-DD guard: date.fromisoformat() accepts compact 20260422 and
# ISO week dates, so a shape check gates before parsing (codex P2-2).
ISO_DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")

PIPELINE_SKILL_NAME = "academic-pipeline"


def _parse_iso_date(raw: str) -> date | None:
    """Strict YYYY-MM-DD → date, else None (bad shape OR impossible date like
    2026-02-30). Never raises — a release lint reports drift, never crashes."""
    if not ISO_DATE_RE.match(raw):
        return None
    try:
        return date.fromisoformat(raw)
    except ValueError:
        return None


def _version_tuple(token: str) -> tuple[int, ...]:
    """Parse a canonical N.N.N(.N) into an int tuple for ordering."""
    return tuple(int(p) for p in token.split("."))


def _version_le(a: str, b: str) -> bool:
    """a <= b by segment-wise numeric compare (pads shorter with zeros)."""
    ta, tb = _version_tuple(a), _version_tuple(b)
    n = max(len(ta), len(tb))
    return ta + (0,) * (n - len(ta)) <= tb + (0,) * (n - len(tb))


def _is_strict_semver(token: str) -> bool:
    return bool(SEMVER_STRICT_RE.match(token))


def _parse_table_versions(
    claude_md_text: str,
) -> tuple[dict[str, str], list[tuple[str, str]]]:
    """Return (valid_versions, invalid_rows) from the Skills Overview table.

    `valid_versions` maps skill_name -> version for rows whose v-token is a
    canonical N.N.N(.N)+ string. `invalid_rows` collects (skill_name, raw_token)
    for rows where the v-token is present but not a canonical version; the
    caller surfaces these as errors so a malformed table row does not silently
    drop out of downstream invariants.
    """
    valid: dict[str, str] = {}
    invalid: list[tuple[str, str]] = []
    for skill, raw in TABLE_TOKEN_RE.findall(claude_md_text):
        if _is_strict_semver(raw):
            valid[skill] = raw
        else:
            invalid.append((skill, raw))
    return valid, invalid


def _parse_suite_version(claude_md_text: str) -> tuple[str | None, str | None]:
    """Return (valid_version, invalid_raw_token).

    Exactly one of the two is non-None when a Suite version line is present.
    Both are None when the line is missing entirely.
    """
    m = SUITE_TOKEN_RE.search(claude_md_text)
    if m is None:
        return None, None
    raw = m.group(1)
    if _is_strict_semver(raw):
        return raw, None
    return None, raw


def _parse_changelog_latest(
    changelog_text: str,
) -> tuple[str | None, str | None, str | None, str]:
    """Return (valid_latest, invalid_raw_token, latest_date, latest_body).

    Walks `## [TOKEN]` headings in document order, skipping pseudo-entries
    like `[Unreleased]`. The first remaining heading is the latest release.
    If that heading's token is not a canonical version, it is returned as
    `invalid_raw_token` so the caller flags it instead of silently falling
    through to a predecessor and hiding the malformed release entry.

    For a valid latest entry, `latest_date` is the heading's YYYY-MM-DD (None
    when absent — invariant 10 flags that) and `latest_body` is the text up to
    the next release heading (invariant 9); `### ` sub-headings and any `## `
    line inside a fenced code block stay INSIDE the body.
    """
    for m in CHANGELOG_TOKEN_RE.finditer(changelog_text):
        raw = m.group(1)
        if raw in NON_VERSION_CHANGELOG_TOKENS:
            continue
        if not _is_strict_semver(raw):
            return None, raw, None, ""
        line_end = changelog_text.find("\n", m.end())
        if line_end == -1:
            line_end = len(changelog_text)
        heading_line = changelog_text[m.start():line_end]
        date_m = CHANGELOG_DATE_RE.search(heading_line)
        body = changelog_text[line_end : _next_entry_offset(changelog_text, line_end)]
        return raw, None, date_m.group(1) if date_m else None, body
    return None, None, None, ""


def _next_entry_offset(text: str, start: int) -> int:
    """Offset of the next release heading (`## [`) at or after `start`, skipping
    any that fall inside a ``` fenced code block. A code sample in the release
    notes can contain a line that looks exactly like a release heading (even
    `## [example] - 2020-01-01`), which must NOT truncate the entry body
    (codex P2-1 + re-review). Returns len(text) when none remains."""
    in_fence = False
    i = start
    n = len(text)
    while i < n:
        line_end = text.find("\n", i)
        if line_end == -1:
            line_end = n
        line = text[i:line_end]
        stripped = line.lstrip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            in_fence = not in_fence
        elif not in_fence and NEXT_ENTRY_RE.match(line):
            return i
        i = line_end + 1
    return n


def check(root: Path, tag: str | None = None) -> list[str]:
    errors: list[str] = []

    claude_md = root / ".claude" / "CLAUDE.md"
    if not claude_md.is_file():
        errors.append(f"{claude_md}: not found")
        return errors
    claude_text = claude_md.read_text(encoding="utf-8")

    table_versions, invalid_table_rows = _parse_table_versions(claude_text)
    if not table_versions and not invalid_table_rows:
        errors.append(
            f"{claude_md}: Skills Overview table has no parseable "
            "`<skill>` vX.Y.Z rows"
        )
    for skill, raw in invalid_table_rows:
        errors.append(
            f"{claude_md}: table row {skill!r} has invalid version "
            f"token v{raw!r} (expected canonical N.N.N or N.N.N.N)"
        )

    suite_version, invalid_suite_token = _parse_suite_version(claude_text)
    if suite_version is None and invalid_suite_token is None:
        errors.append(
            f"{claude_md}: missing '**Suite version**: X.Y.Z' line"
        )
    elif invalid_suite_token is not None:
        errors.append(
            f"{claude_md}: Suite version token {invalid_suite_token!r} is "
            "not a canonical N.N.N or N.N.N.N version"
        )

    changelog = root / "CHANGELOG.md"
    latest_date: str | None = None
    latest: str | None = None
    if not changelog.is_file():
        errors.append(f"{changelog}: not found")
    else:
        latest, invalid_latest, latest_date, latest_body = (
            _parse_changelog_latest(changelog.read_text(encoding="utf-8"))
        )
        if latest is None and invalid_latest is None:
            errors.append(f"{changelog}: no '## [X.Y.Z]' entry found")
        elif invalid_latest is not None:
            errors.append(
                f"{changelog}: latest entry token {invalid_latest!r} is "
                "not a canonical N.N.N or N.N.N.N version"
            )
        elif suite_version is not None and latest != suite_version:
            errors.append(
                f"{claude_md}: Suite version {suite_version!r} does not match "
                f"CHANGELOG latest entry {latest!r}"
            )
        # Invariant 9: the latest entry must carry real release notes.
        if latest is not None:
            body_len = len(latest_body.strip())
            if body_len < CHANGELOG_BODY_MIN_CHARS:
                errors.append(
                    f"{changelog}: latest entry [{latest}] body is {body_len} "
                    f"chars — release notes must be >= "
                    f"{CHANGELOG_BODY_MIN_CHARS} chars"
                )

    # Invariant 10: .claude/CLAUDE.md "Last Updated" within ±7 days of the
    # latest CHANGELOG entry's date. Skipped while the CHANGELOG itself is
    # missing/malformed — those already errored above.
    if latest is not None:
        errors.extend(
            _check_last_updated_freshness(
                claude_md, claude_text, changelog, latest_date
            )
        )

    for skill_name, table_version in sorted(table_versions.items()):
        skill_md = root / skill_name / "SKILL.md"
        if not skill_md.is_file():
            errors.append(
                f"{claude_md}: table lists {skill_name!r} v{table_version} "
                f"but {skill_md} does not exist"
            )
            continue
        try:
            fm = parse_frontmatter(skill_md)
        except FrontmatterError as exc:
            errors.append(str(exc))
            continue
        if fm is None:
            errors.append(f"{skill_md}: missing YAML frontmatter")
            continue
        metadata = fm.get("metadata") or {}
        declared = metadata.get("version")
        if declared is None:
            errors.append(f"{skill_md}: metadata.version is missing")
            continue
        declared_str = str(declared)
        if declared_str != table_version:
            errors.append(
                f"{claude_md}: {skill_name!r} listed as v{table_version} but "
                f"{skill_md} metadata.version is {declared_str!r}"
            )

    if suite_version is not None:
        pipeline_in_table = table_versions.get(PIPELINE_SKILL_NAME)
        if pipeline_in_table is not None and pipeline_in_table != suite_version:
            errors.append(
                f"{claude_md}: {PIPELINE_SKILL_NAME} listed as "
                f"v{pipeline_in_table} but suite version is {suite_version!r} "
                "(pipeline tracks the suite release)"
            )

    # Invariant 4: plugin manifests track the suite version (outward-facing
    # package metadata). Only checked when a suite version is known.
    if suite_version is not None:
        errors.extend(_check_plugin_manifests(root, suite_version))
        # Invariant 5: README version badge tracks the suite version.
        errors.extend(_check_readme_badge(root, suite_version))
        # Invariant 6: docs/ must not cite a version above the suite version.
        errors.extend(_check_docs_versions(root, suite_version))
        # Invariant 11: newest Key Additions heading matches the suite version.
        errors.extend(_check_key_additions(claude_md, claude_text, suite_version))

    # Tag gate: the pushed tag (when given) must equal the suite version. This
    # runs OUTSIDE the `suite_version is not None` block on purpose: `--tag`
    # promises the tag is verified at tag time, so a missing/malformed suite
    # version must surface as "tag uncheckable" (a hard error naming the tag),
    # never a silent pass — otherwise a garbage tag co-occurring with a broken
    # CLAUDE.md would slip through the one gate meant to catch it.
    if tag is not None:
        tag_version = tag[1:] if tag.startswith("v") else tag
        if suite_version is None:
            errors.append(
                f"tag {tag!r} cannot be verified: .claude/CLAUDE.md has no "
                "usable Suite version to compare against (fix the suite "
                "version before tagging)"
            )
        elif tag_version != suite_version:
            errors.append(
                f"tag {tag!r} does not match suite version "
                f"{suite_version!r} (CHANGELOG latest entry / "
                ".claude/CLAUDE.md must be promoted before tagging)"
            )

    # Invariant 7: en<->zh-TW version-bearing-heading parity (independent of
    # suite version; pairs each docs/*.md with its docs/*.zh-TW.md sibling).
    errors.extend(_check_zhtw_heading_parity(root))

    # Invariant 8: plugin.json "N-agent" description claim equals the tree's
    # unique *_agent.md count (independent of suite version).
    errors.extend(_check_agent_count_claim(root))

    return errors


def _check_plugin_manifests(root: Path, suite_version: str) -> list[str]:
    """Invariant 4: .claude-plugin/plugin.json "version" and every
    .claude-plugin/marketplace.json plugins[].version equal the suite version.
    Missing files / malformed JSON / missing version keys are surfaced, never
    crash (a release lint must report drift, not blow up on it)."""
    errors: list[str] = []

    plugin_json = root / ".claude-plugin" / "plugin.json"
    if not plugin_json.is_file():
        errors.append(f"{plugin_json}: not found")
    else:
        try:
            data = json.loads(plugin_json.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, ValueError) as exc:
            errors.append(f"{plugin_json}: invalid JSON ({exc})")
        else:
            v = data.get("version")
            if v is None:
                errors.append(f"{plugin_json}: missing 'version' key")
            elif str(v) != suite_version:
                errors.append(
                    f"{plugin_json}: version {str(v)!r} does not match suite "
                    f"version {suite_version!r}"
                )

    marketplace = root / ".claude-plugin" / "marketplace.json"
    if not marketplace.is_file():
        errors.append(f"{marketplace}: not found")
    else:
        try:
            data = json.loads(marketplace.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, ValueError) as exc:
            errors.append(f"{marketplace}: invalid JSON ({exc})")
        else:
            plugins = data.get("plugins")
            if not isinstance(plugins, list) or not plugins:
                errors.append(f"{marketplace}: 'plugins' is missing or empty")
            else:
                for i, entry in enumerate(plugins):
                    v = (entry or {}).get("version") if isinstance(entry, dict) else None
                    if v is None:
                        errors.append(
                            f"{marketplace}: plugins[{i}] missing 'version' key"
                        )
                    elif str(v) != suite_version:
                        errors.append(
                            f"{marketplace}: plugins[{i}] version {str(v)!r} does "
                            f"not match suite version {suite_version!r}"
                        )

    return errors


def _check_readme_badge(root: Path, suite_version: str) -> list[str]:
    """Invariant 5: README.md shields.io version badge equals the suite version.

    The badge is outward-facing — the first thing a reader sees. A v3.10.0
    release-doc pass can miss it the same way it missed the marketplace
    manifest (invariant 4). Missing file / no badge surfaced, never crash."""
    errors: list[str] = []
    readme = root / "README.md"
    if not readme.is_file():
        errors.append(f"{readme}: not found")
        return errors
    text = readme.read_text(encoding="utf-8")
    matches = README_BADGE_RE.findall(text)
    if not matches:
        errors.append(f"{readme}: no `badge/version-vX.Y.Z` version badge found")
        return errors
    for raw in matches:
        if raw != suite_version:
            errors.append(
                f"{readme}: version badge v{raw} does not match suite "
                f"version {suite_version!r}"
            )
    return errors


def _check_docs_versions(root: Path, suite_version: str) -> list[str]:
    """Invariant 6: no docs/*.md cites a version ABOVE the suite version.

    A doc that references a not-yet-released (or deleted) version is a forward
    reference that misleads readers. Equal-to-suite is fine (<=). Non-canonical
    tokens are surfaced, not silently dropped."""
    errors: list[str] = []
    docs = root / "docs"
    if not docs.is_dir():
        return errors  # docs/ optional; absence is not drift
    for md in sorted(docs.rglob("*.md")):
        # docs/superpowers/ holds skill working files (specs/plans) that
        # deliberately plan the NEXT release — forward references are their
        # job, not a published-doc drift. Invariant 6 gates published docs.
        if "superpowers" in md.relative_to(docs).parts:
            continue
        text = md.read_text(encoding="utf-8")
        for raw in DOCS_VERSION_RE.findall(text):
            if not _is_strict_semver(raw):
                continue  # 2-segment etc. — not a release token we gate on
            if not _version_le(raw, suite_version):
                errors.append(
                    f"{md}: cites v{raw} which is ABOVE suite version "
                    f"{suite_version!r} (forward/unknown reference)"
                )
    return errors


def _version_bearing_headings(text: str) -> Counter:
    """Count version tokens across H2s that carry a vX.Y.Z tag.

    Returns a multiset {version: count}. Comparison is by version token, not
    heading text, so an en heading and its zh-TW translation match despite
    different wording. A MULTISET (not a set/dict) is load-bearing: two H2s in
    one doc tagged the same version count as two, so a translator dropping one
    of a duplicated pair surfaces as a count mismatch (review finding — a
    {version: heading} dict silently collapsed duplicates and passed)."""
    out: Counter = Counter()
    for h in H2_RE.findall(text):
        m = H2_VERSION_RE.search(h)
        if m:
            out[m.group(1)] += 1
    return out


def _check_zhtw_heading_parity(root: Path) -> list[str]:
    """Invariant 7: every version-bearing H2 in docs/<name>.md has a matching
    version-bearing H2 in docs/<name>.zh-TW.md (same version), and vice versa.

    Plain (no-version) headings may differ freely — translation asymmetry is
    allowed; only version TAGS must stay in lockstep. Compares by version-token
    MULTISET, so wording differences don't false-flag but a dropped/added/
    drifted version tag (including one of a same-version pair) does."""
    errors: list[str] = []
    docs = root / "docs"
    if not docs.is_dir():
        return errors
    for zh in sorted(docs.rglob("*.zh-TW.md")):
        en = zh.with_name(zh.name.replace(".zh-TW.md", ".md"))
        if not en.is_file():
            errors.append(f"{zh}: no English sibling {en.name}")
            continue
        en_vers = _version_bearing_headings(en.read_text(encoding="utf-8"))
        zh_vers = _version_bearing_headings(zh.read_text(encoding="utf-8"))
        # Counter subtraction keeps only positive surpluses; doing it both ways
        # surfaces under- and over-translation, and a 2-vs-1 same-version
        # mismatch shows as a residual count of 1.
        for v, n in sorted((en_vers - zh_vers).items()):
            errors.append(
                f"{zh.name}: missing {n} version-bearing heading(s) for v{v} "
                f"present in {en.name}"
            )
        for v, n in sorted((zh_vers - en_vers).items()):
            errors.append(
                f"{zh.name}: has {n} heading(s) citing v{v} not present in "
                f"{en.name} — version drift"
            )
    return errors


def _check_last_updated_freshness(
    claude_md: Path,
    claude_text: str,
    changelog: Path,
    latest_date: str | None,
) -> list[str]:
    """Invariant 10: the "Last Updated" date in .claude/CLAUDE.md lies within
    ±7 days of the latest CHANGELOG entry's date. The CHANGELOG date is the
    baseline — never "today" — so the same commit checks identically whenever
    the lint re-runs."""
    m = LAST_UPDATED_RE.search(claude_text)
    if m is None:
        return [
            f"{claude_md}: missing '- **Last Updated**: YYYY-MM-DD' line"
        ]
    raw = m.group(1)
    last_updated = _parse_iso_date(raw)
    if last_updated is None:
        return [
            f"{claude_md}: Last Updated {raw!r} is not a valid YYYY-MM-DD date"
        ]
    if latest_date is None:
        return [
            f"{changelog}: latest entry has no '- YYYY-MM-DD' date — cannot "
            "check Last Updated freshness against it"
        ]
    changelog_date = _parse_iso_date(latest_date)
    if changelog_date is None:
        return [
            f"{changelog}: latest entry date {latest_date!r} is not a valid "
            "YYYY-MM-DD date"
        ]
    delta = abs((last_updated - changelog_date).days)
    if delta > LAST_UPDATED_MAX_DAYS:
        return [
            f"{claude_md}: Last Updated {raw} is {delta} days from the "
            f"CHANGELOG latest entry date {latest_date} (must be within "
            f"±{LAST_UPDATED_MAX_DAYS} days)"
        ]
    return []


def _check_key_additions(
    claude_md: Path, claude_text: str, suite_version: str
) -> list[str]:
    """Invariant 11: the newest version-tagged "Key Additions" H2 in
    .claude/CLAUDE.md matches the suite version. Newest = max by version
    tuple (the sections are not guaranteed document-ordered). Comparison is
    at the heading's own precision, so `## v3.14 Key Additions` matches suite
    3.14.0 while a stale `## v3.13 ...` as the maximum fails. Historical
    headings below the newest are untouched."""
    versions = KEY_ADDITIONS_RE.findall(claude_text)
    if not versions:
        return [
            f"{claude_md}: no '## vX.Y… Key Additions' heading found — the "
            "release's Key Additions section is missing"
        ]
    newest = max(versions, key=_version_tuple)
    newest_t = _version_tuple(newest)
    if _version_tuple(suite_version)[: len(newest_t)] != newest_t:
        return [
            f"{claude_md}: newest Key Additions heading cites v{newest} but "
            f"the suite version is {suite_version!r}"
        ]
    return []


def _check_agent_count_claim(root: Path) -> list[str]:
    """Invariant 8 (#414): when plugin.json's description advertises an
    "N-agent" count, N must equal the number of unique *_agent.md files in
    the tree. The plugin-root agents/ mirror dir is excluded — its files are
    byte-identical aliases of deep-research agents (real copies since #413,
    symlinks before; check_agents_mirror_sync.py pins the byte-equality), so
    counting them would double-count. resolve() additionally dedups any
    remaining symlink alias. Missing/malformed manifest or a description
    without a count claim is NOT an invariant-8 error — the manifest problems
    are invariant 4's to report, and the claim is optional (only a stated
    number must be true)."""
    plugin_json = root / ".claude-plugin" / "plugin.json"
    if not plugin_json.is_file():
        return []
    try:
        data = json.loads(plugin_json.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, ValueError):
        return []
    description = data.get("description")
    if not isinstance(description, str):
        return []
    m = AGENT_CLAIM_RE.search(description)
    if m is None:
        return []
    claimed = int(m.group(1))
    actual = len({
        p.resolve()
        for p in root.rglob("*_agent.md")
        if ".git" not in p.parts
        and p.relative_to(root).parts[0] != "agents"  # plugin-root mirror = aliases (#413)
    })
    if claimed != actual:
        return [
            f"{plugin_json}: description claims {claimed}-agent but the tree "
            f"has {actual} unique *_agent.md files (agents/ mirror aliases "
            f"excluded, symlinks deduplicated)"
        ]
    return []


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--path",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
    )
    parser.add_argument(
        "--tag",
        help="git tag ref (e.g. v3.14.0, leading 'v' optional); must equal "
        "the suite version — used by the tag-version-match workflow",
    )
    args = parser.parse_args()

    errors = check(args.path, tag=args.tag)
    if errors:
        print("Version consistency check failed:")
        for err in errors:
            print(f"- {err}")
        return 1
    print("Version consistency check passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
