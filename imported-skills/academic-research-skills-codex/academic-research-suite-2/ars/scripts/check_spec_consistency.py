#!/usr/bin/env python3

from __future__ import annotations

from fnmatch import fnmatch
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ERRORS: list[str] = []
MARKDOWN_LINK_RE = re.compile(r"\[[^\]]+\]\(([^)]+)\)")


def codex_manifest() -> dict[str, object]:
    manifest_path = ROOT.parent / "manifest.json"
    if not manifest_path.is_file():
        return {}
    try:
        doc = json.loads(manifest_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        fail(f"{manifest_path.relative_to(ROOT.parent)}: invalid JSON: {exc}")
        return {}
    if not isinstance(doc, dict):
        fail(f"{manifest_path.relative_to(ROOT.parent)}: expected JSON object")
        return {}
    return doc


def is_codex_distribution() -> bool:
    return codex_manifest().get("generated_for") == "codex"


def codex_excluded_patterns() -> tuple[str, ...]:
    manifest = codex_manifest()
    if manifest.get("generated_for") != "codex":
        return ()
    patterns = manifest.get("excluded_patterns", [])
    if not isinstance(patterns, list):
        fail("manifest.json: excluded_patterns must be a list")
        return ()
    return tuple(pattern for pattern in patterns if isinstance(pattern, str))


def is_intentionally_excluded(rel_path: str) -> bool:
    for pattern in codex_excluded_patterns():
        prefix = pattern.rstrip("/")
        if rel_path == prefix or rel_path.startswith(prefix + "/") or fnmatch(rel_path, pattern):
            return True
    return False


def entry_path(rel_path: str) -> str:
    if is_codex_distribution():
        return rel_path.replace("/SKILL.md", "/WORKFLOW.md")
    return rel_path


def read(rel_path: str) -> str:
    return (ROOT / rel_path).read_text(encoding="utf-8")


def fail(message: str) -> None:
    ERRORS.append(message)


def expect_contains(rel_path: str, needle: str) -> None:
    text = read(rel_path)
    if needle not in text:
        fail(f"{rel_path}: missing expected text: {needle!r}")


def expect_absent(rel_path: str, needle: str) -> None:
    text = read(rel_path)
    if needle in text:
        fail(f"{rel_path}: forbidden text still present: {needle!r}")


def extract_section(text: str, start: str, end: str) -> str:
    start_idx = text.find(start)
    if start_idx == -1:
        fail(f"missing section start: {start!r}")
        return ""
    end_idx = text.find(end, start_idx + len(start))
    if end_idx == -1:
        fail(f"missing section end after {start!r}: {end!r}")
        return text[start_idx:]
    return text[start_idx:end_idx]


def check_relative_markdown_links(rel_path: str) -> None:
    text = read(rel_path)
    doc_path = ROOT / rel_path
    for raw_target in MARKDOWN_LINK_RE.findall(text):
        if raw_target.startswith(("http://", "https://", "mailto:", "#")):
            continue
        target = raw_target.split("#", 1)[0]
        if not target:
            continue
        resolved = (doc_path.parent / target).resolve()
        if not resolved.exists():
            try:
                target_rel = resolved.relative_to(ROOT).as_posix()
            except ValueError:
                target_rel = ""
            if target_rel and is_intentionally_excluded(target_rel):
                continue
            fail(f"{rel_path}: broken relative markdown link {raw_target!r}")


def check_mode_registry() -> None:
    rel_path = "MODE_REGISTRY.md"
    text = read(rel_path)
    expect_contains(rel_path, "Last updated: v3.16.0 (2026-07-12)")
    for heading in (
        "## deep-research (8 modes)",
        "## academic-paper (11 modes)",
        "## academic-paper-reviewer (6 modes)",
    ):
        if heading not in text:
            fail(f"{rel_path}: missing mode heading {heading!r}")


def check_claude_md() -> None:
    rel_path = ".claude/CLAUDE.md"
    if not (ROOT / rel_path).is_file():
        print(f"Skipping {rel_path} checks: file not present in this distribution.")
        return
    expect_contains(rel_path, "integrity check (Stage 2.5)")
    expect_contains(rel_path, "final integrity check (Stage 4.5)")
    expect_contains(rel_path, "**Suite version**: 3.16.0")
    for forbidden in (
        "6th independent reviewer",
        "Peer review gains 6th independent reviewer",
    ):
        expect_absent(rel_path, forbidden)


# All four skills carry the same frontmatter (`version` / `last_updated`) + Version-Info-table
# (`| Skill Version |` / `| Last Updated |`) pair. Pre-#377 only the reviewer was policed.
_SKILL_VERSION_PATHS = (
    "academic-pipeline/SKILL.md",
    "academic-paper/SKILL.md",
    "academic-paper-reviewer/SKILL.md",
    "deep-research/SKILL.md",
)

# The single skill whose `version` tracks the suite version. The other three move independently,
# so only this one's date is sanity-checked against the release (CHANGELOG) in #377(b).
_SUITE_SKILL_PATH = "academic-pipeline/SKILL.md"


def _parse_skill_version_block(rel_path: str) -> tuple[str, str, str, str] | None:
    """Return (frontmatter_version, frontmatter_last_updated, table_version, table_last_updated)
    for a SKILL.md, or None (after recording an error) if any surface is unparseable."""
    text = read(rel_path)
    frontmatter_match = re.search(
        r'metadata:\s*[\s\S]*?\n\s+version:\s"([^"]+)"\n\s+last_updated:\s"([^"]+)"',
        text,
    )
    if not frontmatter_match:
        fail(f"{rel_path}: could not parse frontmatter version/last_updated")
        return None

    version_block_match = re.search(r"\| Skill Version \| ([^|]+) \|", text)
    updated_block_match = re.search(r"\| Last Updated \| ([^|]+) \|", text)
    if not version_block_match or not updated_block_match:
        fail(f"{rel_path}: missing Version Info table rows")
        return None

    version, last_updated = frontmatter_match.groups()
    return (
        version,
        last_updated,
        version_block_match.group(1).strip(),
        updated_block_match.group(1).strip(),
    )


def check_skill_version_blocks() -> None:
    """#377(a): for ALL FOUR SKILL.md, the frontmatter version/last_updated must match the
    Version-Info-table rows (an internal per-file consistency check)."""
    for rel_path in _SKILL_VERSION_PATHS:
        parsed = _parse_skill_version_block(entry_path(rel_path))
        if parsed is None:
            continue
        version, last_updated, version_block, updated_block = parsed
        if version != version_block:
            fail(
                f"{rel_path}: frontmatter version {version!r} does not match Version Info block {version_block!r}"
            )
        if last_updated != updated_block:
            fail(
                f"{rel_path}: frontmatter last_updated {last_updated!r} does not match Version Info block {updated_block!r}"
            )


def _latest_changelog_date() -> str | None:
    """Parse the date of the latest release entry in CHANGELOG.md. The file follows
    Keep-a-Changelog convention — entries are reverse-chronological under a leading
    dateless `## [Unreleased]` header — so the FIRST date-bearing
    `## [X.Y.Z] - YYYY-MM-DD` header is the latest release. `## [Unreleased]` carries no
    `- YYYY-MM-DD` suffix and so never matches this date-bearing pattern."""
    match = re.search(rf"^## \[{_VERSION}\] - (\d{{4}}-\d{{2}}-\d{{2}})", read("CHANGELOG.md"), re.M)
    return match.group(1) if match else None


def check_suite_skill_date_sanity() -> None:
    """#377(b): the suite-tracking skill's `last_updated` must NOT predate the latest CHANGELOG
    entry date — a release that bumps the suite version but forgets the date fails here.

    Scope is deliberately narrow: only `academic-pipeline/SKILL.md` (the suite-tracking skill) is
    date-checked. `academic-paper` / `academic-paper-reviewer` / `deep-research` version
    independently and legitimately keep their own earlier last-change dates, so forcing
    release-date alignment on them would be wrong (#377 out-of-scope)."""
    # check_skill_version_blocks() runs first and already parses the suite SKILL. If it recorded
    # an error for that file (unparseable frontmatter/table), skip rather than re-report the same
    # root cause from a second re-parse here.
    suite_skill_path = entry_path(_SUITE_SKILL_PATH)
    if any(e.startswith(f"{suite_skill_path}:") for e in ERRORS):
        return

    changelog_date = _latest_changelog_date()
    if changelog_date is None:
        fail("CHANGELOG.md: could not parse latest release entry date")
        return

    parsed = _parse_skill_version_block(suite_skill_path)
    if parsed is None:
        return
    last_updated = parsed[1]

    # ISO-8601 dates compare correctly as strings (zero-padded, fixed-width).
    if last_updated < changelog_date:
        fail(
            f"{suite_skill_path}: last_updated {last_updated!r} predates latest CHANGELOG entry "
            f"date {changelog_date!r} — the suite version bumped but the skill date is stale"
        )


def check_pipeline_docs() -> None:
    for rel_path in (
        "academic-pipeline/SKILL.md",
        "academic-pipeline/agents/pipeline_orchestrator_agent.md",
    ):
        rel_path = entry_path(rel_path)
        expect_absent(rel_path, "auto-continue in 5 seconds")
        expect_contains(rel_path, "One-line status + explicit continue/pause prompt")

    expect_contains(
        "academic-pipeline/agents/pipeline_orchestrator_agent.md",
        "Stage 2.5 can NEVER be skipped",
    )
    expect_contains(
        "academic-pipeline/agents/pipeline_orchestrator_agent.md",
        "Stage 4.5 can NEVER be skipped",
    )


# A version token is a dot-separated run of ≥3 numeric components. The repo's own grammar
# already ships 4-component versions (v3.9.4.2), so a fixed `\d+\.\d+\.\d+` would capture only
# the first three components of `3.9.4.2` and silently compare a truncated `3.9.4` — making a
# genuinely-stale 4-component marker pass. `(?:\.\d+)*` is greedy, so it captures the FULL token;
# the trailing `(?!\.?\d)` is a hard right boundary so a longer numeric run can never tail-match a
# shorter capture (e.g. `3.9.4` must not partial-match inside `3.9.4.2`).
_VERSION = r"\d+\.\d+\.\d+(?:\.\d+)*(?!\.?\d)"


def _suite_version() -> str | None:
    """Parse the canonical suite version from `.claude/CLAUDE.md` (`**Suite version**: X.Y.Z[.W]`)."""
    if not (ROOT / ".claude/CLAUDE.md").is_file():
        return None
    match = re.search(rf"\*\*Suite version\*\*:\s*({_VERSION})", read(".claude/CLAUDE.md"))
    return match.group(1) if match else None


def check_architecture_component_version() -> None:
    """Invariant-4 (#345): the *current-component* `academic-pipeline` version markers in
    docs/ARCHITECTURE.md must equal the suite version.

    docs/ARCHITECTURE.md carries two kinds of version string and only the first must track the
    suite version:
      - current-component markers — the mermaid orchestrator node + the component table row + the
        four stage-table `(gate)` / stage-6 rows — describe what the *current* pipeline is.
      - feature-history markers — the `timeline` block (`vX.Y.Z : <feature>`) and inline
        "introduced in vX.Y.Z" provenance — record which version first shipped a gate/feature and
        must NOT be bumped on a release that adds no new gate.

    This check anchors on the `academic-pipeline <ver>` component pattern specifically (mermaid
    `<br/>vX.Y.Z` node + ` academic-pipeline vX.Y.Z` table/stage rows) and never inspects the
    timeline block, so a stale current-component marker fails while a feature-history marker is
    left alone. (Surfaced during the v3.11.1 release: six component markers were missed by the
    bump and only caught by a manual sweep — #343/#344.)
    """
    rel_path = "docs/ARCHITECTURE.md"
    version = _suite_version()
    if version is None:
        if is_codex_distribution():
            print(
                "Skipping docs/ARCHITECTURE.md component-version checks: "
                ".claude/CLAUDE.md is not present in this distribution."
            )
            return
        fail(".claude/CLAUDE.md: could not parse '**Suite version**: X.Y.Z' for ARCHITECTURE check")
        return
    text = read(rel_path)

    # 1. Mermaid orchestrator node: `academic-pipeline<br/>orchestrator<br/>vX.Y.Z`.
    node_versions = re.findall(
        rf"academic-pipeline<br/>orchestrator<br/>v({_VERSION})", text
    )
    if not node_versions:
        fail(f"{rel_path}: no mermaid `academic-pipeline<br/>orchestrator<br/>vX.Y.Z` node found")
    for found in node_versions:
        if found != version:
            fail(
                f"{rel_path}: mermaid orchestrator node version v{found} != suite v{version} "
                f"(invariant-4: current-component marker must equal the suite version)"
            )

    # 2. Component table + stage rows: ` academic-pipeline vX.Y.Z` (table cell / `(gate)` rows).
    #    Anchored to markdown table rows (`^\s*\|` … on the same line) so the scan only ever sees
    #    component/stage cells — never prose like `` `academic-pipeline` v3.9.4 introduced … ``,
    #    which is feature-history provenance and must NOT be policed against the suite version.
    #    The timeline `vX.Y.Z :` form never carries the `academic-pipeline` token, so it is already
    #    out of scope; the table-row anchor additionally excludes any narrative mention.
    row_versions = re.findall(
        rf"(?m)^\s*\|.*?`?academic-pipeline`?\s+v({_VERSION})", text
    )
    if not row_versions:
        fail(f"{rel_path}: no `academic-pipeline vX.Y.Z` component/stage row found")
    for found in row_versions:
        if found != version:
            fail(
                f"{rel_path}: `academic-pipeline v{found}` component/stage row != suite v{version} "
                f"(invariant-4: current-component marker must equal the suite version)"
            )


def check_readme_sections() -> None:
    rel_path = "README.md"
    text = read(rel_path)

    expect_contains(rel_path, "version-v3.16.0-blue")
    expect_contains(rel_path, "releases/tag/v3.16.0")
    expect_contains(rel_path, "### v3.12.0 (2026-06-08)")
    expect_contains(rel_path, "### v3.11.1 (2026-06-06)")
    expect_contains(rel_path, "### v3.11.0 (2026-06-04)")
    expect_contains(rel_path, "### v3.10.0 (2026-06-01)")
    expect_contains(rel_path, "### v3.9.4.2 (2026-05-19)")
    expect_contains(rel_path, "### v3.9.4.1 (2026-05-19)")
    expect_contains(rel_path, "### v3.9.4 (2026-05-18)")
    expect_contains(rel_path, "### v3.9.1 (2026-05-18)")
    expect_contains(rel_path, "### v3.9.0 (2026-05-17)")
    expect_contains(rel_path, "### v3.8.0 (2026-05-16)")
    expect_contains(rel_path, "### v3.7.0 (2026-05-05)")
    expect_contains(rel_path, "### v3.6.8 (2026-05-03)")
    expect_contains(rel_path, "### v3.6.7 (2026-04-30)")
    expect_contains(rel_path, "### v3.6.5 (2026-04-27)")
    expect_contains(rel_path, "### v3.6.4 (2026-04-25)")
    expect_contains(rel_path, "### v3.6.3 (2026-04-23)")
    expect_contains(rel_path, "### v3.6.2 (2026-04-23)")
    expect_contains(rel_path, "### v3.5.1 (2026-04-22)")
    expect_contains(rel_path, "### v3.5.0 (2026-04-21)")
    expect_contains(rel_path, "### v3.4.0 (2026-04-20)")
    expect_contains(rel_path, "### v3.3.6 (2026-04-15)")
    expect_contains(rel_path, "### v3.3.5 (2026-04-15)")
    expect_contains(rel_path, "### v3.3.4 (2026-04-15)")
    expect_contains(rel_path, "### v3.3.3 (2026-04-15)")
    expect_contains(rel_path, "### v3.3.2 (2026-04-15)")
    for heading in (
        "#### Deep Research (8 modes)",
        "#### Academic Paper (11 modes)",
        "#### Academic Paper Reviewer (6 modes)",
        "### Deep Research (v2.11.0)",
        "### Academic Paper (v3.2.0)",
        "### Academic Paper Reviewer (v1.10.0)",
        "### Academic Pipeline (v3.16.0)",
    ):
        if heading not in text:
            fail(f"{rel_path}: missing heading {heading!r}")

    paper_usage = extract_section(
        text, "#### Academic Paper (11 modes)", "#### Academic Paper Reviewer (6 modes)"
    )
    for expected in ("outline-only mode", "abstract-only mode", "disclosure mode"):
        if expected not in paper_usage:
            fail(f"{rel_path}: Academic Paper usage section missing {expected!r}")
    for forbidden in ("bilingual-abstract mode", "writing-polish mode", "full-auto mode"):
        if forbidden in paper_usage:
            fail(f"{rel_path}: Academic Paper usage section still contains {forbidden!r}")

    deep_usage = extract_section(
        text, "#### Deep Research (8 modes)", "#### Academic Paper (11 modes)"
    )
    if "review mode" not in deep_usage:
        fail(f"{rel_path}: Deep Research usage section missing 'review mode'")
    if "paper-review" in deep_usage:
        fail(f"{rel_path}: Deep Research usage section still contains 'paper-review'")

    reviewer_usage = extract_section(
        text, "#### Academic Paper Reviewer (6 modes)", "#### Academic Pipeline (Orchestrator)"
    )
    if "calibration mode" not in reviewer_usage:
        fail(f"{rel_path}: reviewer usage section missing 'calibration mode'")

    for forbidden in (
        "6th independent reviewer",
        "Peer review gains 6th independent reviewer",
    ):
        expect_absent(rel_path, forbidden)
    # DOCX contract lines moved to docs/SETUP.md in v3.3.6; checked there instead.
    expect_contains(rel_path, "DOCX (via Pandoc when available)")
    check_relative_markdown_links(rel_path)


def check_readme_ja_sections() -> None:
    """Symmetric coverage of README.ja-JP.md added in PR #161 (closes #170).

    Pre-#170 the lint silently skipped this file. ja-JP uses ASCII parentheses
    for release blocks (matching the English README), full-width parentheses
    for mode and skill-detail headings, and "モード" instead of "mode".
    """
    rel_path = "README.ja-JP.md"
    text = read(rel_path)

    expect_contains(rel_path, "version-v3.16.0-blue")
    expect_contains(rel_path, "releases/tag/v3.16.0")
    expect_contains(rel_path, "### v3.12.0 (2026-06-08)")
    expect_contains(rel_path, "### v3.11.1 (2026-06-06)")
    expect_contains(rel_path, "### v3.11.0 (2026-06-04)")
    expect_contains(rel_path, "### v3.10.0 (2026-06-01)")
    expect_contains(rel_path, "### v3.9.4.2 (2026-05-19)")
    expect_contains(rel_path, "### v3.9.4.1 (2026-05-19)")
    expect_contains(rel_path, "### v3.9.4 (2026-05-18)")
    expect_contains(rel_path, "### v3.9.1 (2026-05-18)")
    expect_contains(rel_path, "### v3.9.0 (2026-05-17)")
    expect_contains(rel_path, "### v3.8.0 (2026-05-16)")
    expect_contains(rel_path, "### v3.7.0 (2026-05-05)")
    expect_contains(rel_path, "### v3.6.8 (2026-05-03)")
    expect_contains(rel_path, "### v3.6.7 (2026-04-30)")
    expect_contains(rel_path, "### v3.6.5 (2026-04-27)")
    expect_contains(rel_path, "### v3.6.4 (2026-04-25)")
    expect_contains(rel_path, "### v3.6.3 (2026-04-23)")
    expect_contains(rel_path, "### v3.6.2 (2026-04-23)")
    expect_contains(rel_path, "### v3.5.1 (2026-04-22)")
    expect_contains(rel_path, "### v3.5.0 (2026-04-21)")
    expect_contains(rel_path, "### v3.4.0 (2026-04-20)")
    expect_contains(rel_path, "### v3.3.6 (2026-04-15)")
    expect_contains(rel_path, "### v3.3.5 (2026-04-15)")
    expect_contains(rel_path, "### v3.3.4 (2026-04-15)")
    expect_contains(rel_path, "### v3.3.3 (2026-04-15)")
    expect_contains(rel_path, "### v3.3.2 (2026-04-15)")
    for heading in (
        "#### Deep Research（8 モード）",
        "#### Academic Paper（11 モード）",
        "#### Academic Paper Reviewer（6 モード）",
        "#### Academic Pipeline（オーケストレーター）",
        "### Deep Research（v2.11.0）",
        "### Academic Paper（v3.2.0）",
        "### Academic Paper Reviewer（v1.10.0）",
        "### Academic Pipeline（v3.16.0）",
    ):
        if heading not in text:
            fail(f"{rel_path}: missing heading {heading!r}")

    for forbidden in (
        "6th independent reviewer",
        "Peer review gains 6th independent reviewer",
    ):
        expect_absent(rel_path, forbidden)

    # Mode-section content guards (e.g. `outline-only モード` inside the
    # Academic Paper usage block) are deliberately not enforced here; the
    # zh-TW checker uses `extract_section` for that and #171's schema-driven
    # refactor will fold the three locales together. Adding the extract_section
    # mirror now would be discarded by that refactor.
    expect_contains(rel_path, "DOCX（利用可能な場合 Pandoc 経由）")
    check_relative_markdown_links(rel_path)


def check_readme_ko_sections() -> None:
    """Symmetric coverage of README.ko-KR.md added with Korean localization.

    Korean typography uses ASCII parentheses, so the release-block headings match
    the English / ja-JP convention verbatim (NOT the full-width zh-CN/zh-TW form).
    Localized mode headings use ASCII parens + "N개 모드"; skill-detail headings
    reuse the English ASCII-paren form. Mode-section inner-content guards are
    deliberately omitted here, mirroring check_readme_ja_sections — the #171
    schema-driven refactor will fold the locales together, so an extract_section
    mirror added now would be discarded by it.
    """
    rel_path = "README.ko-KR.md"
    text = read(rel_path)

    expect_contains(rel_path, "version-v3.16.0-blue")
    expect_contains(rel_path, "releases/tag/v3.16.0")
    expect_contains(rel_path, "### v3.16.0 (2026-07-12)")
    expect_contains(rel_path, "### v3.12.0 (2026-06-08)")
    expect_contains(rel_path, "### v3.11.1 (2026-06-06)")
    expect_contains(rel_path, "### v3.11.0 (2026-06-04)")
    expect_contains(rel_path, "### v3.10.0 (2026-06-01)")
    expect_contains(rel_path, "### v3.9.4.2 (2026-05-19)")
    expect_contains(rel_path, "### v3.9.4.1 (2026-05-19)")
    expect_contains(rel_path, "### v3.9.4 (2026-05-18)")
    expect_contains(rel_path, "### v3.9.1 (2026-05-18)")
    expect_contains(rel_path, "### v3.9.0 (2026-05-17)")
    expect_contains(rel_path, "### v3.8.0 (2026-05-16)")
    expect_contains(rel_path, "### v3.7.0 (2026-05-05)")
    expect_contains(rel_path, "### v3.6.8 (2026-05-03)")
    expect_contains(rel_path, "### v3.6.7 (2026-04-30)")
    expect_contains(rel_path, "### v3.6.5 (2026-04-27)")
    expect_contains(rel_path, "### v3.6.4 (2026-04-25)")
    expect_contains(rel_path, "### v3.6.3 (2026-04-23)")
    expect_contains(rel_path, "### v3.6.2 (2026-04-23)")
    expect_contains(rel_path, "### v3.5.1 (2026-04-22)")
    expect_contains(rel_path, "### v3.5.0 (2026-04-21)")
    expect_contains(rel_path, "### v3.4.0 (2026-04-20)")
    expect_contains(rel_path, "### v3.3.6 (2026-04-15)")
    expect_contains(rel_path, "### v3.3.5 (2026-04-15)")
    expect_contains(rel_path, "### v3.3.4 (2026-04-15)")
    expect_contains(rel_path, "### v3.3.3 (2026-04-15)")
    expect_contains(rel_path, "### v3.3.2 (2026-04-15)")
    for heading in (
        "#### Deep Research (8개 모드)",
        "#### Academic Paper (11개 모드)",
        "#### Academic Paper Reviewer (6개 모드)",
        "#### Academic Pipeline (오케스트레이터)",
        "### Deep Research (v2.11.0)",
        "### Academic Paper (v3.2.0)",
        "### Academic Paper Reviewer (v1.10.0)",
        "### Academic Pipeline (v3.16.0)",
    ):
        if heading not in text:
            fail(f"{rel_path}: missing heading {heading!r}")

    for forbidden in (
        "6th independent reviewer",
        "Peer review gains 6th independent reviewer",
    ):
        expect_absent(rel_path, forbidden)

    expect_contains(rel_path, "DOCX (가능한 경우 Pandoc 경유)")
    check_relative_markdown_links(rel_path)


ZH_README_CONFIGS = (
    {
        "rel_path": "README.zh-TW.md",
        "headings": (
            "#### Deep Research（深度研究，8 種模式）",
            "#### Academic Paper（學術論文撰寫，11 種模式）",
            "#### Academic Paper Reviewer（論文審查，6 種模式）",
            "### Deep Research (v2.11.0)",
            "### Academic Paper (v3.2.0)",
            "### Academic Paper Reviewer (v1.10.0)",
            "### Academic Pipeline (v3.16.0)",
        ),
        "paper_start": "#### Academic Paper（學術論文撰寫，11 種模式）",
        "reviewer_start": "#### Academic Paper Reviewer（論文審查，6 種模式）",
        "pipeline_start": "#### Academic Pipeline（全流程調度器）",
        "deep_start": "#### Deep Research（深度研究，8 種模式）",
        "docx_line": "DOCX（Pandoc 可用時）",
    },
    {
        "rel_path": "README.zh-CN.md",
        "headings": (
            "#### Deep Research（深度研究，8 种模式）",
            "#### Academic Paper（学术论文撰写，11 种模式）",
            "#### Academic Paper Reviewer（论文审查，6 种模式）",
            "### Deep Research (v2.11.0)",
            "### Academic Paper (v3.2.0)",
            "### Academic Paper Reviewer (v1.10.0)",
            "### Academic Pipeline (v3.16.0)",
        ),
        "paper_start": "#### Academic Paper（学术论文撰写，11 种模式）",
        "reviewer_start": "#### Academic Paper Reviewer（论文审查，6 种模式）",
        "pipeline_start": "#### Academic Pipeline（全流程调度器）",
        "deep_start": "#### Deep Research（深度研究，8 种模式）",
        "docx_line": "DOCX（Pandoc 可用时）",
    },
)


def check_readme_zh_sections() -> None:
    for config in ZH_README_CONFIGS:
        rel_path = config["rel_path"]
        text = read(rel_path)

        expect_contains(rel_path, "version-v3.16.0-blue")
        expect_contains(rel_path, "releases/tag/v3.16.0")
        expect_contains(rel_path, "### v3.12.0（2026-06-08）")
        expect_contains(rel_path, "### v3.11.1（2026-06-06）")
        expect_contains(rel_path, "### v3.11.0（2026-06-04）")
        expect_contains(rel_path, "### v3.10.0（2026-06-01）")
        expect_contains(rel_path, "### v3.9.4.2（2026-05-19）")
        expect_contains(rel_path, "### v3.9.4.1（2026-05-19）")
        expect_contains(rel_path, "### v3.9.4（2026-05-18）")
        expect_contains(rel_path, "### v3.9.1（2026-05-18）")
        expect_contains(rel_path, "### v3.9.0（2026-05-17）")
        expect_contains(rel_path, "### v3.8.0（2026-05-16）")
        expect_contains(rel_path, "### v3.7.0（2026-05-05）")
        expect_contains(rel_path, "### v3.6.8（2026-05-03）")
        expect_contains(rel_path, "### v3.6.7（2026-04-30）")
        expect_contains(rel_path, "### v3.6.5（2026-04-27）")
        expect_contains(rel_path, "### v3.6.4（2026-04-25）")
        expect_contains(rel_path, "### v3.6.3（2026-04-23）")
        expect_contains(rel_path, "### v3.6.2（2026-04-23）")
        expect_contains(rel_path, "### v3.5.1（2026-04-22）")
        expect_contains(rel_path, "### v3.5.0（2026-04-21）")
        expect_contains(rel_path, "### v3.4.0（2026-04-20）")
        expect_contains(rel_path, "### v3.3.6 (2026-04-15)")
        expect_contains(rel_path, "### v3.3.5 (2026-04-15)")
        expect_contains(rel_path, "### v3.3.4 (2026-04-15)")
        expect_contains(rel_path, "### v3.3.3 (2026-04-15)")
        expect_contains(rel_path, "### v3.3.2 (2026-04-15)")
        for heading in config["headings"]:
            if heading not in text:
                fail(f"{rel_path}: missing heading {heading!r}")

        paper_usage = extract_section(
            text,
            config["paper_start"],
            config["reviewer_start"],
        )
        for expected in ("outline-only mode", "abstract-only mode", "disclosure mode"):
            if expected not in paper_usage:
                fail(f"{rel_path}: Academic Paper usage section missing {expected!r}")
        for forbidden in ("bilingual-abstract mode", "writing-polish mode", "full-auto mode"):
            if forbidden in paper_usage:
                fail(f"{rel_path}: Academic Paper usage section still contains {forbidden!r}")

        deep_usage = extract_section(
            text,
            config["deep_start"],
            config["paper_start"],
        )
        if "review mode" not in deep_usage:
            fail(f"{rel_path}: Deep Research usage section missing 'review mode'")
        if "paper-review" in deep_usage:
            fail(f"{rel_path}: Deep Research usage section still contains 'paper-review'")

        reviewer_usage = extract_section(
            text,
            config["reviewer_start"],
            config["pipeline_start"],
        )
        if "calibration mode" not in reviewer_usage:
            fail(f"{rel_path}: reviewer usage section missing 'calibration mode'")

        for forbidden in (
            "6th independent reviewer",
            "Peer review gains 6th independent reviewer",
        ):
            expect_absent(rel_path, forbidden)
        # DOCX contract lines moved to setup docs in v3.3.6; checked there instead.
        expect_contains(rel_path, config["docx_line"])
        check_relative_markdown_links(rel_path)


def check_setup_docs() -> None:
    expect_contains("docs/SETUP.md", "Direct `.docx` generation uses [Pandoc]")
    expect_contains(
        "docs/SETUP.md",
        "Direct `.docx` generation requires Pandoc, and PDF generation requires `tectonic`",
    )
    expect_contains("docs/SETUP.zh-TW.md", "若要直接產出 `.docx`，需要安裝 [Pandoc]")
    expect_contains(
        "docs/SETUP.zh-TW.md",
        "直接產出 `.docx` 需要 Pandoc，PDF 需要 `tectonic`",
    )
    check_relative_markdown_links("docs/SETUP.md")
    check_relative_markdown_links("docs/SETUP.zh-TW.md")


def check_docx_contract() -> None:
    expect_contains(
        entry_path("academic-paper/SKILL.md"),
        "LaTeX/DOCX-via-Pandoc/PDF output",
    )
    expect_contains(
        "academic-paper/agents/formatter_agent.md",
        "If Pandoc is available, generate the `.docx` file directly",
    )
    expect_contains(
        "academic-paper/agents/formatter_agent.md",
        "If Pandoc is unavailable, provide complete markdown + DOCX conversion instructions",
    )
    expect_contains(
        entry_path("academic-pipeline/SKILL.md"),
        "DOCX via Pandoc when available, otherwise conversion instructions",
    )
    expect_contains(
        "academic-pipeline/agents/pipeline_orchestrator_agent.md",
        "DOCX via Pandoc when available (otherwise instructions)",
    )
    for rel_path in (
        "academic-pipeline/SKILL.md",
        "academic-pipeline/agents/pipeline_orchestrator_agent.md",
    ):
        rel_path = entry_path(rel_path)
        expect_absent(rel_path, "Auto-produce MD + DOCX")


def check_reference_docs() -> None:
    expect_contains(
        "academic-pipeline/references/passport_as_reset_boundary.md",
        "# Passport as Reset Boundary (v3.6.3)",
    )
    expect_contains(
        "academic-pipeline/references/passport_as_reset_boundary.md",
        "## `resume_from_passport` mode contract",
    )
    expect_contains(
        "academic-pipeline/references/passport_as_reset_boundary.md",
        "## Iron rules",
    )
    # Unified PASSPORT-RESET tag format across protocol doc + orchestrator emission + checkpoint template.
    # Divergence here breaks cross-session machine-stable handoff.
    tag_format = "[PASSPORT-RESET: hash=<hash>, stage=<completed>, next=<next>]"
    expect_contains(
        "academic-pipeline/references/passport_as_reset_boundary.md",
        tag_format,
    )
    expect_contains(
        "academic-pipeline/agents/pipeline_orchestrator_agent.md",
        tag_format,
    )


def check_rebuttal_audit_guard() -> None:
    """The rebuttal-audit mode section must declare its integrity boundary.

    A standalone rebuttal-audit invocation runs outside the pipeline, so it must
    NOT emit Schema 11 / Material Passport / ready_to_submit. This guard is the
    load-bearing reason rebuttal-audit is safe to ship as a mode rather than a
    pipeline stage; if the suppression language is ever dropped, the mode would
    silently re-introduce the false-certification risk it was designed to avoid.
    """
    logical_rel_path = "academic-paper/SKILL.md"
    try:
        rel_path = logical_rel_path
        text = read(logical_rel_path)
    except FileNotFoundError:
        rel_path = entry_path(logical_rel_path)
        text = read(rel_path)
    m = re.search(r"##\s*Rebuttal-Audit Mode.*?(?=\n##\s|\Z)", text, re.DOTALL)
    section = m.group(0) if m else ""
    if not section:
        fail(f"{rel_path}: missing '## Rebuttal-Audit Mode' section")
        return
    for kw in ["Schema 11", "Material Passport", "ready_to_submit"]:
        if kw not in section:
            fail(
                f"{rel_path} Rebuttal-Audit Mode section must declare "
                f"{kw!r} suppression (integrity boundary)"
            )
    if "MUST NOT" not in section:
        fail(
            f"{rel_path} Rebuttal-Audit Mode section lacks an explicit "
            "'MUST NOT' suppression statement"
        )


def main() -> int:
    check_mode_registry()
    check_claude_md()
    check_skill_version_blocks()
    check_suite_skill_date_sanity()
    check_pipeline_docs()
    check_architecture_component_version()
    check_readme_sections()
    check_readme_zh_sections()
    check_readme_ja_sections()
    check_readme_ko_sections()
    check_setup_docs()
    check_docx_contract()
    check_reference_docs()
    check_rebuttal_audit_guard()

    if ERRORS:
        print("Spec consistency check failed:")
        for error in ERRORS:
            print(f"- {error}")
        return 1

    print("Spec consistency check passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
