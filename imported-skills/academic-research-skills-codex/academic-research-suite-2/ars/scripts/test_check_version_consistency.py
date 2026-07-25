"""Unit tests for check_version_consistency.py."""
from __future__ import annotations

import subprocess
import textwrap
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script

SCRIPT = Path(__file__).resolve().parent / "check_version_consistency.py"


def _run(root: Path) -> subprocess.CompletedProcess:
    return run_script(SCRIPT, "--path", str(root))


def _write_skill(root: Path, name: str, version: str) -> None:
    skill_dir = root / name
    skill_dir.mkdir(parents=True, exist_ok=True)
    (skill_dir / "SKILL.md").write_text(
        textwrap.dedent(
            f"""\
            ---
            name: {name}
            description: "fixture"
            metadata:
              version: "{version}"
              last_updated: "2026-04-22"
              status: active
              data_access_level: raw
              task_type: open-ended
            ---

            # {name}
            """
        ),
        encoding="utf-8",
    )


def _write_claude_md(
    root: Path,
    suite_version: str,
    table_rows: list[tuple[str, str]],
    last_updated: str | None = "2026-04-22",
    key_additions: str | None = "derive",
) -> None:
    """`last_updated` / `key_additions` default to values aligned with the
    fixture CHANGELOG (invariants 10 + 11). `key_additions="derive"` writes a
    `## v<major>.<minor> Key Additions` heading derived from `suite_version`;
    pass an explicit token (e.g. "v3.4") to drift it, or None to omit."""
    claude_dir = root / ".claude"
    claude_dir.mkdir(parents=True, exist_ok=True)
    rows = "\n".join(
        f"| `{name}` v{ver} | purpose | modes |" for name, ver in table_rows
    )
    if key_additions == "derive":
        parts = suite_version.split(".")
        if len(parts) >= 2 and all(p.isdigit() for p in parts[:2]):
            key_additions = f"v{parts[0]}.{parts[1]}"
        else:
            key_additions = None
    key_additions_block = (
        f"## {key_additions} Key Additions (fixture)\n\n- fixture addition\n\n"
        if key_additions is not None
        else ""
    )
    last_updated_line = (
        f"- **Last Updated**: {last_updated}\n" if last_updated is not None else ""
    )
    text = (
        "# Academic Research Skills\n"
        "\n"
        "## Skills Overview\n"
        "\n"
        "| Skill | Purpose | Key Modes |\n"
        "|-------|---------|-----------|\n"
        f"{rows}\n"
        "\n"
        f"{key_additions_block}"
        "## Version Info\n"
        f"- **Suite version**: {suite_version} (per CHANGELOG.md)\n"
        f"{last_updated_line}"
    )
    (claude_dir / "CLAUDE.md").write_text(text, encoding="utf-8")


def _write_changelog(
    root: Path,
    latest_version: str,
    prior_versions: list[str] | None = None,
    latest_body: str | None = None,
    latest_date: str = "2026-04-22",
) -> None:
    """Write fixture CHANGELOG with `latest_version` first, then any `prior_versions`.

    The default latest-entry body is long enough to satisfy the >=100-char
    release-notes invariant (9); pass a short `latest_body` to drift it."""
    if latest_body is None:
        latest_body = (
            "### Added\n"
            "- fixture entry with enough substantive body text that the latest "
            "release entry clears the one-hundred-character release-notes "
            "minimum enforced by invariant 9\n"
        )
    entries = [f"## [{latest_version}] - {latest_date}\n\n{latest_body}"]
    for prev in prior_versions or []:
        entries.append(f"## [{prev}] - 2026-04-15\n\n### Added\n- prior fixture entry\n")
    (root / "CHANGELOG.md").write_text(
        "# Changelog\n\n" + "\n".join(entries),
        encoding="utf-8",
    )


def _write_plugin_manifests(
    root: Path, version: str, description: str | None = None
) -> None:
    """Fixture .claude-plugin/{plugin,marketplace}.json at `version` (invariant 4).
    `description` (when given) lands in plugin.json for the invariant-8
    "N-agent" claim tests."""
    import json
    plugin_dir = root / ".claude-plugin"
    plugin_dir.mkdir(parents=True, exist_ok=True)
    plugin_obj: dict[str, str] = {"name": "fixture", "version": version}
    if description is not None:
        plugin_obj["description"] = description
    (plugin_dir / "plugin.json").write_text(
        json.dumps(plugin_obj), encoding="utf-8"
    )
    (plugin_dir / "marketplace.json").write_text(
        json.dumps({"name": "fixture", "plugins": [{"name": "fixture", "version": version}]}),
        encoding="utf-8",
    )


def _write_readme(root: Path, badge_version: str) -> None:
    """Fixture README.md with a shields.io version badge (invariant 5).

    The badge encodes the version twice (label + release-tag URL); the lint
    keys off the `badge/version-vX.Y.Z` label, the canonical surface a user
    sees. Both are written aligned here so drift tests mutate one explicitly.
    """
    (root / "README.md").write_text(
        "# Academic Research Skills for Claude Code\n"
        "\n"
        f"[![Version](https://img.shields.io/badge/version-v{badge_version}-blue)]"
        f"(https://github.com/x/y/releases/tag/v{badge_version})\n",
        encoding="utf-8",
    )


def _write_docs(
    root: Path,
    en_h2: list[str],
    zh_h2: list[str] | None = None,
    extra_version_strings: list[str] | None = None,
) -> None:
    """Fixture docs/ tree (invariants 6 + 7).

    `en_h2` / `zh_h2` are H2 heading texts (without the leading '## ').
    Version-bearing headings like 'Foo (v3.6.4+)' exercise the en<->zh-TW
    heading-pairing invariant; plain headings are ignored by it. Any
    `extra_version_strings` are dropped into PERFORMANCE.md body to exercise
    the 'docs must not cite a future/unknown version' invariant.
    """
    docs = root / "docs"
    docs.mkdir(parents=True, exist_ok=True)
    en_body = "\n".join(f"## {h}\n\nbody\n" for h in en_h2)
    if extra_version_strings:
        en_body += "\n" + "\n".join(f"See v{v} for details.\n" for v in extra_version_strings)
    (docs / "PERFORMANCE.md").write_text("# Performance\n\n" + en_body, encoding="utf-8")
    if zh_h2 is not None:
        zh_body = "\n".join(f"## {h}\n\n內文\n" for h in zh_h2)
        (docs / "PERFORMANCE.zh-TW.md").write_text("# 效能\n\n" + zh_body, encoding="utf-8")


def _write_aligned_fixture(
    root: Path,
    last_updated: str | None = "2026-04-22",
    key_additions: str | None = "derive",
) -> None:
    """Everything lines up — baseline for PASS cases and drift mutations.

    `last_updated` / `key_additions` pass straight through to `_write_claude_md`
    so invariant-10 / invariant-11 tests can drift a single field without
    re-specifying the aligned skill table (which would duplicate the very
    drift this lint exists to catch)."""
    skills = [
        ("deep-research", "2.9.0"),
        ("academic-paper", "3.1.0"),
        ("academic-paper-reviewer", "1.8.1"),
        ("academic-pipeline", "3.5.0"),
    ]
    for name, ver in skills:
        _write_skill(root, name, ver)
    _write_claude_md(
        root,
        suite_version="3.5.0",
        table_rows=skills,
        last_updated=last_updated,
        key_additions=key_additions,
    )
    _write_changelog(root, latest_version="3.5.0")
    _write_plugin_manifests(root, "3.5.0")
    _write_readme(root, "3.5.0")
    # en has an extra plain H2 (translation asymmetry is allowed); the
    # version-bearing heading is present in both and at a past version.
    _write_docs(
        root,
        en_h2=["Token usage", "Corpus ingestion (v3.4.0+)", "Extra EN-only section"],
        zh_h2=["Token 用量", "語料庫導入 (v3.4.0+)"],
        extra_version_strings=["3.4.0"],
    )


def _write_aligned_fixture_v351(root: Path) -> None:
    """v3.5.1 suite: deep-research 2.9.1, academic-pipeline 3.5.1."""
    skills = [
        ("deep-research", "2.9.1"),
        ("academic-paper", "3.1.0"),
        ("academic-paper-reviewer", "1.8.1"),
        ("academic-pipeline", "3.5.1"),
    ]
    for name, ver in skills:
        _write_skill(root, name, ver)
    _write_claude_md(root, suite_version="3.5.1", table_rows=skills)
    _write_changelog(root, latest_version="3.5.1")
    _write_plugin_manifests(root, "3.5.1")
    _write_readme(root, "3.5.1")
    _write_docs(
        root,
        en_h2=["Token usage", "Corpus ingestion (v3.4.0+)"],
        zh_h2=["Token 用量", "語料庫導入 (v3.4.0+)"],
        extra_version_strings=["3.4.0", "3.5.1"],
    )


class TestVersionConsistency(unittest.TestCase):
    def test_all_aligned_passes(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            result = _run(root)
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )

    def test_all_aligned_v351_passes(self) -> None:
        """v3.5.1 suite (deep-research 2.9.1, academic-pipeline 3.5.1) must pass."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture_v351(root)
            result = _run(root)
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )

    def test_table_version_drift_fails(self) -> None:
        """Table lists deep-research v2.9.0 but SKILL.md says 2.8.0 — must fail."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_skill(root, "deep-research", "2.8.0")
            result = _run(root)
            self.assertEqual(result.returncode, 1)
            self.assertIn("deep-research", result.stdout)
            self.assertIn("2.9.0", result.stdout)
            self.assertIn("2.8.0", result.stdout)

    def test_suite_version_vs_changelog_drift_fails(self) -> None:
        """CLAUDE.md suite version != CHANGELOG latest entry — must fail."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_changelog(root, latest_version="3.4.0")
            result = _run(root)
            self.assertEqual(result.returncode, 1)
            self.assertIn("3.5.0", result.stdout)
            self.assertIn("3.4.0", result.stdout)
            self.assertIn("CHANGELOG", result.stdout)

    def test_plugin_json_version_drift_fails(self) -> None:
        """Invariant 4: .claude-plugin/plugin.json version != suite — must fail.
        (Regression for the v3.10.0 release miss: plugin.json sat at the prior
        version because no lint covered it.)"""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)  # suite 3.5.0
            _write_plugin_manifests(root, "3.4.0")  # drift both manifests down
            result = _run(root)
            self.assertEqual(result.returncode, 1)
            self.assertIn("plugin.json", result.stdout)
            self.assertIn("3.4.0", result.stdout)
            self.assertIn("3.5.0", result.stdout)

    def test_marketplace_version_drift_fails(self) -> None:
        """Invariant 4: marketplace.json plugins[].version != suite — must fail.
        (Regression for marketplace.json silently sitting at 3.7.0 for releases.)"""
        import json
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)  # suite 3.5.0; plugin.json aligned at 3.5.0
            # Drift ONLY marketplace, leaving plugin.json correct, to isolate it.
            (root / ".claude-plugin" / "marketplace.json").write_text(
                json.dumps({"name": "fixture",
                            "plugins": [{"name": "fixture", "version": "3.7.0"}]}),
                encoding="utf-8",
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1)
            self.assertIn("marketplace.json", result.stdout)
            self.assertIn("3.7.0", result.stdout)

    def test_pipeline_version_vs_suite_drift_fails(self) -> None:
        """academic-pipeline version in table must equal suite version."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            # Drop pipeline to 3.4.0 in both table and SKILL.md, keep suite at 3.5.0.
            # This isolates invariant 3 (pipeline tracks suite) from invariant 1
            # (SKILL.md == table).
            _write_skill(root, "academic-pipeline", "3.4.0")
            _write_claude_md(
                root,
                suite_version="3.5.0",
                table_rows=[
                    ("deep-research", "2.9.0"),
                    ("academic-paper", "3.1.0"),
                    ("academic-paper-reviewer", "1.8.1"),
                    ("academic-pipeline", "3.4.0"),
                ],
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1)
            self.assertIn("academic-pipeline", result.stdout)

    def test_skill_missing_frontmatter_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            (root / "deep-research" / "SKILL.md").write_text(
                "# deep-research\n\nNo frontmatter here.\n",
                encoding="utf-8",
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1)
            self.assertIn("deep-research", result.stdout)

    def test_skill_listed_in_table_but_missing_on_disk_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            import shutil
            shutil.rmtree(root / "academic-paper-reviewer")
            result = _run(root)
            self.assertEqual(result.returncode, 1)
            self.assertIn("academic-paper-reviewer", result.stdout)

    def test_missing_suite_version_in_claude_md_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            (root / ".claude" / "CLAUDE.md").write_text(
                textwrap.dedent(
                    """\
                    # Academic Research Skills

                    ## Skills Overview

                    | Skill | Purpose | Key Modes |
                    |-------|---------|-----------|
                    | `deep-research` v2.9.0 | x | y |
                    | `academic-paper` v3.1.0 | x | y |
                    | `academic-paper-reviewer` v1.8.1 | x | y |
                    | `academic-pipeline` v3.5.0 | x | y |

                    ## Version Info
                    - No suite version line here.
                    """
                ),
                encoding="utf-8",
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1)
            self.assertIn("Suite version", result.stdout)

    def test_four_segment_suite_vs_changelog_drift_fails(self) -> None:
        """Regression for #169: 4-segment hotfix versions (e.g. 3.9.4.1 vs 3.9.4.2)
        must not be silently parsed as a shared 3-segment prefix.

        Scenario: suite claims v3.9.4.2 but CHANGELOG's latest entry is v3.9.4.1.
        Pre-fix behavior: both got truncated to "3.9.4" and the lint passed silently.
        """
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            skills = [
                ("deep-research", "2.9.4"),
                ("academic-paper", "3.1.2"),
                ("academic-paper-reviewer", "1.9.1"),
                ("academic-pipeline", "3.9.4.2"),
            ]
            for name, ver in skills:
                _write_skill(root, name, ver)
            _write_claude_md(root, suite_version="3.9.4.2", table_rows=skills)
            # Include the 3-segment ancestor so the pre-fix regex would still find
            # *something* and silently report a passing 3.9.4 == 3.9.4 comparison.
            _write_changelog(
                root, latest_version="3.9.4.1", prior_versions=["3.9.4"],
            )
            result = _run(root)
            self.assertEqual(
                result.returncode, 1,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )
            self.assertIn("3.9.4.2", result.stdout)
            self.assertIn("3.9.4.1", result.stdout)
            self.assertIn("CHANGELOG", result.stdout)

    def test_five_segment_changelog_does_not_silently_fall_through(self) -> None:
        """Regression for dual-track review of #169: an N+1 segment latest
        entry (e.g. 3.9.4.2.1) must not silently skip to the next valid
        3-or-4 segment predecessor. Pre-fix CHANGELOG_ENTRY_RE failed on
        the 5-segment heading and `re.search` fell through to a predecessor;
        if that predecessor happened to equal the suite version, the lint
        reported PASS even though the actual latest release was a different
        version."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            skills = [
                ("deep-research", "2.9.4"),
                ("academic-paper", "3.1.2"),
                ("academic-paper-reviewer", "1.9.1"),
                ("academic-pipeline", "3.9.4.2"),
            ]
            for name, ver in skills:
                _write_skill(root, name, ver)
            _write_claude_md(root, suite_version="3.9.4.2", table_rows=skills)
            _write_changelog(
                root, latest_version="3.9.4.2.1", prior_versions=["3.9.4.2"],
            )
            result = _run(root)
            self.assertEqual(
                result.returncode, 1,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )
            self.assertIn("3.9.4.2.1", result.stdout)
            # Either path is acceptable surfacing: either the suite-vs-CHANGELOG
            # mismatch (if the new 5-seg token is itself accepted as canonical
            # under the broadened validator) or an invalid-token report.
            self.assertTrue(
                "does not match CHANGELOG latest entry" in result.stdout
                or "canonical" in result.stdout,
                msg=f"expected either drift or invalid-token surface: {result.stdout!r}",
            )

    def test_invalid_table_row_token_is_reported(self) -> None:
        """Regression for dual-track review of #169: a table row carrying a
        non-canonical version token (e.g. v3.9.4.2-alpha or v3.9.4.2.1) must
        surface as an error. Pre-fix: TABLE_ROW_RE failed and the row silently
        vanished from table_versions, so invariant 3 (pipeline tracks suite)
        was skipped because `pipeline_in_table` ended up None."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            skills_on_disk = [
                ("deep-research", "2.9.4"),
                ("academic-paper", "3.1.2"),
                ("academic-paper-reviewer", "1.9.1"),
                ("academic-pipeline", "3.9.4.2"),
            ]
            for name, ver in skills_on_disk:
                _write_skill(root, name, ver)
            table_rows_with_junk = [
                ("deep-research", "2.9.4"),
                ("academic-paper", "3.1.2"),
                ("academic-paper-reviewer", "1.9.1"),
                ("academic-pipeline", "3.9.4.2-alpha"),  # invalid token
            ]
            _write_claude_md(
                root, suite_version="3.9.4.2", table_rows=table_rows_with_junk
            )
            _write_changelog(
                root, latest_version="3.9.4.2", prior_versions=["3.9.4"],
            )
            result = _run(root)
            self.assertEqual(
                result.returncode, 1,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )
            self.assertIn("academic-pipeline", result.stdout)
            self.assertIn("3.9.4.2-alpha", result.stdout)
            self.assertIn("canonical", result.stdout)

    def test_invalid_suite_token_is_reported(self) -> None:
        """Regression for dual-track review of #169: a non-canonical suite
        version token (e.g. 3.9.4.2-alpha) must surface as an error rather
        than being partially captured as 3.9.4.2 via prefix match."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            skills = [
                ("deep-research", "2.9.4"),
                ("academic-paper", "3.1.2"),
                ("academic-paper-reviewer", "1.9.1"),
                ("academic-pipeline", "3.9.4.2"),
            ]
            for name, ver in skills:
                _write_skill(root, name, ver)
            _write_claude_md(
                root, suite_version="3.9.4.2-alpha", table_rows=skills
            )
            _write_changelog(
                root, latest_version="3.9.4.2", prior_versions=["3.9.4"],
            )
            result = _run(root)
            self.assertEqual(
                result.returncode, 1,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )
            self.assertIn("3.9.4.2-alpha", result.stdout)
            self.assertIn("canonical", result.stdout)

    def test_four_segment_table_row_drift_fails(self) -> None:
        """Regression for #169: the Skills table row regex must also see the 4th
        segment, so a pipeline row v3.9.4.1 vs suite version 3.9.4.2 is caught."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            # Pipeline SKILL.md and CHANGELOG both at 3.9.4.2, but the table row
            # in CLAUDE.md still says v3.9.4.1 (forgot to bump one place).
            skills_on_disk = [
                ("deep-research", "2.9.4"),
                ("academic-paper", "3.1.2"),
                ("academic-paper-reviewer", "1.9.1"),
                ("academic-pipeline", "3.9.4.2"),
            ]
            for name, ver in skills_on_disk:
                _write_skill(root, name, ver)
            table_rows_drifted = [
                ("deep-research", "2.9.4"),
                ("academic-paper", "3.1.2"),
                ("academic-paper-reviewer", "1.9.1"),
                ("academic-pipeline", "3.9.4.1"),  # drift inside the 4th segment
            ]
            _write_claude_md(
                root, suite_version="3.9.4.2", table_rows=table_rows_drifted
            )
            _write_changelog(
                root, latest_version="3.9.4.2", prior_versions=["3.9.4"],
            )
            result = _run(root)
            self.assertEqual(
                result.returncode, 1,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )
            self.assertIn("academic-pipeline", result.stdout)
            self.assertIn("3.9.4.1", result.stdout)
            self.assertIn("3.9.4.2", result.stdout)

    def test_five_segment_token_rejected_as_non_canonical(self) -> None:
        """Regression for #178: post-ship codex review of PR #173 flagged that
        SEMVER_STRICT_RE used `{2,}` (3 or more dot segments) with no upper
        bound, so a 5-segment token like 3.9.4.2.1 passed the canonical check
        even though the file-level docstrings and #173 design defined canonical
        as N.N.N or N.N.N.N. If a 5-segment typo were copied consistently to
        CLAUDE.md, CHANGELOG.md, and the pipeline table, the lint would have
        passed despite the malformed shape. Cap to {2,3}: 4 segments max."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            # All four sources self-consistent on a 5-segment typo. Pre-fix:
            # all three regexes captured "3.9.4.2.1" verbatim, _is_strict_semver
            # returned True (matched {2,} = 3 or more segments), and every
            # invariant compared two identical strings — lint reported PASS
            # even though the shape was malformed. Post-fix: SEMVER_STRICT_RE
            # rejects 5+ segments, so the suite, table row, and CHANGELOG
            # entry all surface as "canonical" violations.
            skills_5seg = [
                ("deep-research", "2.9.4"),
                ("academic-paper", "3.1.2"),
                ("academic-paper-reviewer", "1.9.1"),
                ("academic-pipeline", "3.9.4.2.1"),
            ]
            for name, ver in skills_5seg:
                _write_skill(root, name, ver)
            _write_claude_md(
                root, suite_version="3.9.4.2.1", table_rows=skills_5seg
            )
            _write_changelog(
                root, latest_version="3.9.4.2.1", prior_versions=["3.9.4.2"],
            )
            result = _run(root)
            self.assertEqual(
                result.returncode, 1,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )
            self.assertIn("3.9.4.2.1", result.stdout)
            self.assertIn("canonical", result.stdout)

    # ── Invariant 5: README version badge tracks the suite version ──────────
    def test_readme_badge_drift_fails(self) -> None:
        """README shields.io version badge drifts below suite version — must fail."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_readme(root, "3.4.0")  # badge stale vs suite 3.5.0
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("README", result.stdout)
            self.assertIn("3.4.0", result.stdout)

    def test_readme_missing_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            (root / "README.md").unlink()
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("README", result.stdout)

    # ── Invariant 6: docs/ must not cite a version above the suite version ──
    def test_docs_future_version_fails(self) -> None:
        """docs/ references v9.9.9 (above suite 3.5.0) — must fail."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_docs(
                root,
                en_h2=["Token usage", "Corpus ingestion (v3.4.0+)"],
                zh_h2=["Token 用量", "語料庫導入 (v3.4.0+)"],
                extra_version_strings=["9.9.9"],  # future / nonexistent
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("9.9.9", result.stdout)

    def test_docs_at_suite_version_passes_inv6(self) -> None:
        """A docs version string EQUAL to the suite version is allowed (<=)."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_docs(
                root,
                en_h2=["Token usage", "Corpus ingestion (v3.4.0+)"],
                zh_h2=["Token 用量", "語料庫導入 (v3.4.0+)"],
                extra_version_strings=["3.5.0"],  # == suite, must be OK
            )
            result = _run(root)
            self.assertEqual(result.returncode, 0, msg=f"stdout={result.stdout!r}")

    def test_docs_superpowers_future_version_exempt_inv6(self) -> None:
        """docs/superpowers/ holds skill specs/plans that intentionally plan the
        NEXT release; a future version there is exempt (must PASS). A non-aligned
        future version anywhere ELSE in docs/ still fails — proves the carve-out
        is scoped to superpowers/, not a blanket disable."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)  # suite 3.5.0
            sp = root / "docs" / "superpowers" / "plans"
            sp.mkdir(parents=True, exist_ok=True)
            (sp / "next-release-plan.md").write_text(
                "# Plan\n\nBump suite to v9.9.9 in this release.\n", encoding="utf-8"
            )
            result = _run(root)
            self.assertEqual(
                result.returncode, 0,
                msg=f"superpowers/ future ref should be exempt; stdout={result.stdout!r}",
            )
            # control: same future token under a published doc path still fails
            (root / "docs" / "OTHER.md").write_text(
                "# Other\n\nSee v9.9.9 here.\n", encoding="utf-8"
            )
            result2 = _run(root)
            self.assertEqual(result2.returncode, 1, msg=f"stdout={result2.stdout!r}")
            self.assertIn("9.9.9", result2.stdout)

    # ── Invariant 7: en<->zh-TW version-bearing H2 + version-string parity ──
    def test_zhtw_version_bearing_heading_missing_fails(self) -> None:
        """en has '(v3.4.0+)' heading; zh-TW drops it — must fail."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_docs(
                root,
                en_h2=["Token usage", "Corpus ingestion (v3.4.0+)"],
                zh_h2=["Token 用量", "語料庫導入"],  # version tag dropped
                extra_version_strings=["3.4.0"],
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("zh-TW", result.stdout)

    def test_zhtw_version_bearing_heading_drift_fails(self) -> None:
        """en heading says v3.4.0, zh-TW says v3.3.0 — version drift, must fail."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_docs(
                root,
                en_h2=["Token usage", "Corpus ingestion (v3.4.0+)"],
                zh_h2=["Token 用量", "語料庫導入 (v3.3.0+)"],  # drift
                extra_version_strings=["3.4.0"],
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")

    def test_zhtw_plain_heading_asymmetry_allowed(self) -> None:
        """en may have extra PLAIN (no-version) H2 the zh-TW lacks — must pass."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            # aligned fixture already has en-only 'Extra EN-only section'; assert it passes
            result = _run(root)
            self.assertEqual(result.returncode, 0, msg=f"stdout={result.stdout!r}")

    def test_docs_two_segment_version_is_skipped(self) -> None:
        """inv 6 gates only on full N.N.N tokens; a 2-segment `v9.9` in docs is
        not a release token this lint adjudicates, so it must NOT fail even
        though 9.9 > suite 3.5.0 (review test-gap)."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            docs = root / "docs"
            (docs / "PERFORMANCE.md").write_text(
                "# Performance\n\n## Token usage\n\nSee v9.9 milestone.\n"
                "## Corpus ingestion (v3.4.0+)\n\nbody\n",
                encoding="utf-8",
            )
            (docs / "PERFORMANCE.zh-TW.md").write_text(
                "# 效能\n\n## Token 用量\n\n看 v9.9 里程碑。\n"
                "## 語料庫導入 (v3.4.0+)\n\n內文\n",
                encoding="utf-8",
            )
            result = _run(root)
            self.assertEqual(result.returncode, 0, msg=f"stdout={result.stdout!r}")

    def test_docs_prerelease_token_is_skipped(self) -> None:
        """`v3.12.0-alpha` (above suite) must NOT partial-match to 3.12.0 and
        fail — non-canonical tokens are dropped entirely (review finding)."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            (root / "docs" / "PERFORMANCE.md").write_text(
                "# Performance\n\n## Token usage\n\nWork toward v3.12.0-alpha.\n"
                "## Corpus ingestion (v3.4.0+)\n\nbody\n",
                encoding="utf-8",
            )
            (root / "docs" / "PERFORMANCE.zh-TW.md").write_text(
                "# 效能\n\n## Token 用量\n\n邁向 v3.12.0-alpha。\n"
                "## 語料庫導入 (v3.4.0+)\n\n內文\n",
                encoding="utf-8",
            )
            result = _run(root)
            self.assertEqual(result.returncode, 0, msg=f"stdout={result.stdout!r}")

    def test_zhtw_no_english_sibling_fails(self) -> None:
        """A standalone docs/*.zh-TW.md with no .md sibling — must fail (review test-gap)."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            (root / "docs" / "ORPHAN.zh-TW.md").write_text(
                "# 孤兒\n\n## 一節 (v3.4.0+)\n\n內文\n", encoding="utf-8"
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("sibling", result.stdout)

    def test_zhtw_duplicate_same_version_heading_drop_fails(self) -> None:
        """en has TWO H2s tagged v3.4.0; zh-TW translates only one. Multiset
        comparison must catch the dropped duplicate (review finding; a
        {version: heading} dict silently collapsed this and passed)."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            (root / "docs" / "PERFORMANCE.md").write_text(
                "# Performance\n\n## Feature A (v3.4.0+)\n\nbody\n"
                "## Feature B (v3.4.0+)\n\nbody\n",
                encoding="utf-8",
            )
            (root / "docs" / "PERFORMANCE.zh-TW.md").write_text(
                "# 效能\n\n## 功能 A (v3.4.0+)\n\n內文\n",  # only ONE translated
                encoding="utf-8",
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("3.4.0", result.stdout)


class TestAgentCountClaim(unittest.TestCase):
    """Invariant 8 (#414): plugin.json description "N-agent" claim equals the
    tree's unique *_agent.md count (symlinks resolved, not double-counted)."""

    @staticmethod
    def _write_agents(root: Path, names: list[str]) -> None:
        agents_dir = root / "deep-research" / "agents"
        agents_dir.mkdir(parents=True, exist_ok=True)
        for name in names:
            (agents_dir / f"{name}_agent.md").write_text(
                f"# {name}\n", encoding="utf-8"
            )

    def test_agent_claim_drift_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_plugin_manifests(
                root, "3.5.0", description="fixture, 3-agent ensemble, more"
            )
            self._write_agents(root, ["alpha", "beta"])
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("3-agent", result.stdout)
            self.assertIn("2", result.stdout)

    def test_agent_claim_matching_passes(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_plugin_manifests(
                root, "3.5.0", description="fixture, 2-agent ensemble, more"
            )
            self._write_agents(root, ["alpha", "beta"])
            result = _run(root)
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )

    def test_agent_claim_symlink_alias_not_double_counted(self) -> None:
        """Legacy/transition pin: a symlink alias in the plugin-root agents/
        dir (the pre-#413 pattern) still counts once — the whole root
        agents/ mirror is excluded from the count regardless of file kind."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_plugin_manifests(
                root, "3.5.0", description="fixture, 2-agent ensemble, more"
            )
            self._write_agents(root, ["alpha", "beta"])
            link_dir = root / "agents"
            link_dir.mkdir()
            (link_dir / "alpha_agent.md").symlink_to(
                root / "deep-research" / "agents" / "alpha_agent.md"
            )
            result = _run(root)
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )

    def test_agent_claim_materialized_mirror_not_double_counted(self) -> None:
        """#413: the plugin-root agents/ mirror holds REAL byte-identical
        copies (symlinks broke Windows checkouts / zip installs), so resolve()
        no longer dedups them. The mirror dir is excluded from the count —
        it is an alias surface pinned byte-identical to its deep-research
        sources by check_agents_mirror_sync.py, never a source of new
        agents."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_plugin_manifests(
                root, "3.5.0", description="fixture, 2-agent ensemble, more"
            )
            self._write_agents(root, ["alpha", "beta"])
            mirror_dir = root / "agents"
            mirror_dir.mkdir()
            src = root / "deep-research" / "agents" / "alpha_agent.md"
            (mirror_dir / "alpha_agent.md").write_bytes(src.read_bytes())
            result = _run(root)
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )

    def test_no_agent_claim_skips(self) -> None:
        """A description without an N-agent token is not gated (the claim is
        optional; only a stated number must be true)."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_plugin_manifests(
                root, "3.5.0", description="fixture without a count claim"
            )
            self._write_agents(root, ["alpha", "beta"])
            result = _run(root)
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )


class TestChangelogBodyLength(unittest.TestCase):
    """Invariant 9 (#487): the latest CHANGELOG entry's body must be >= 100
    characters — a bare heading (or a stub line) is not release notes."""

    def test_short_body_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_changelog(root, latest_version="3.5.0", latest_body="- stub\n")
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("body", result.stdout)
            self.assertIn("100", result.stdout)

    def test_empty_body_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_changelog(root, latest_version="3.5.0", latest_body="\n")
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("body", result.stdout)

    def test_prior_entry_body_not_gated(self) -> None:
        """Only the LATEST entry is gated — historical entries may be terse."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_changelog(root, latest_version="3.5.0", prior_versions=["3.4.0"])
            result = _run(root)
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )

    def test_fenced_h2_inside_body_not_a_terminator(self) -> None:
        """A '## ' line inside a fenced code block must NOT truncate the body
        (codex P2-1): the entry body ends at the next RELEASE heading, not any
        markdown H2. Otherwise a code sample in the release notes false-fails
        invariant 9."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            body = (
                "### Added\n\n"
                "```md\n"
                "## not a release heading — just a code sample\n"
                "```\n\n"
                "Real release notes continue here with more than one hundred "
                "characters of substantive text so invariant 9 is satisfied by "
                "the full body, not the truncated fence prefix.\n"
            )
            _write_changelog(
                root, latest_version="3.5.0", latest_body=body,
                prior_versions=["3.4.0"],
            )
            result = _run(root)
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )

    def test_fenced_bracketed_h2_not_a_terminator(self) -> None:
        """A fenced '## [example]' — which even LOOKS like a release heading —
        must not truncate the body either (codex re-review): the body ends at
        the next real release heading, past any fenced content."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            body = (
                "### Added\n\n"
                "```md\n"
                "## [example] - 2020-01-01 — a code sample, not a real entry\n"
                "```\n\n"
                "Real release notes continue here with more than one hundred "
                "characters of substantive text so invariant 9 is satisfied by "
                "the full body, not the truncated fence prefix.\n"
            )
            _write_changelog(
                root, latest_version="3.5.0", latest_body=body,
                prior_versions=["3.4.0"],
            )
            result = _run(root)
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )


class TestLastUpdatedFreshness(unittest.TestCase):
    """Invariant 10 (#487): .claude/CLAUDE.md "Last Updated" must lie within
    ±7 days of the latest CHANGELOG entry's date (deterministic baseline —
    re-running the lint later cannot flip the result)."""

    def test_stale_last_updated_fails(self) -> None:
        """8 days after the CHANGELOG date (2026-04-22) is out of the window."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root, last_updated="2026-04-30")
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("Last Updated", result.stdout)

    def test_boundary_seven_days_passes(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root, last_updated="2026-04-29")
            result = _run(root)
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )

    def test_missing_last_updated_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root, last_updated=None)
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("Last Updated", result.stdout)

    def test_changelog_missing_date_fails(self) -> None:
        """The latest entry carrying no date breaks the freshness baseline."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            # Strip only the date off the aligned CHANGELOG heading, keeping
            # the compliant body so invariant 9 doesn't also fire.
            changelog = root / "CHANGELOG.md"
            changelog.write_text(
                changelog.read_text(encoding="utf-8").replace(
                    "## [3.5.0] - 2026-04-22", "## [3.5.0]"
                ),
                encoding="utf-8",
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("date", result.stdout)

    def test_impossible_changelog_date_reports_not_crashes(self) -> None:
        """A syntactically-shaped but impossible CHANGELOG date (2026-02-30)
        must produce a lint error, never a traceback (codex P2-2)."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            _write_changelog(root, latest_version="3.5.0", latest_date="2026-02-30")
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertNotIn("Traceback", result.stderr)
            self.assertIn("2026-02-30", result.stdout)

    def test_overlong_changelog_date_not_accepted_as_prefix(self) -> None:
        """A trailing-digit date like 2026-04-222 must NOT be prefix-captured
        as 2026-04-22 and silently pass freshness (codex re-review P3): it is
        malformed and must be flagged."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root, last_updated="2026-04-22")
            _write_changelog(root, latest_version="3.5.0", latest_date="2026-04-222")
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertNotIn("Traceback", result.stderr)

    def test_non_iso_last_updated_reports_not_crashes(self) -> None:
        """A non-YYYY-MM-DD Last Updated that date.fromisoformat happens to
        accept (e.g. compact 20260422) must still be flagged as malformed
        rather than silently passing (codex P2-2)."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root, last_updated="20260422")
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("Last Updated", result.stdout)


class TestKeyAdditionsAlignment(unittest.TestCase):
    """Invariant 11 (#487): the newest "## vX.Y… Key Additions" heading in
    .claude/CLAUDE.md must match the suite version (compared at the heading's
    own precision, so `## v3.5 Key Additions` matches suite 3.5.0)."""

    def test_key_additions_drift_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root, key_additions="v3.4")
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("Key Additions", result.stdout)

    def test_key_additions_missing_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root, key_additions=None)
            result = _run(root)
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("Key Additions", result.stdout)

    def test_three_segment_heading_match_passes(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root, key_additions="v3.5.0")
            result = _run(root)
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )

    def test_older_headings_below_newest_allowed(self) -> None:
        """Historical Key Additions sections stay put; only the NEWEST (max
        version) heading is compared against the suite version."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            claude_md = root / ".claude" / "CLAUDE.md"
            text = claude_md.read_text(encoding="utf-8")
            text = text.replace(
                "## Version Info\n",
                "## v3.4 Key Additions (older, allowed)\n\n- old\n\n## Version Info\n",
            )
            claude_md.write_text(text, encoding="utf-8")
            result = _run(root)
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )


class TestTagMatch(unittest.TestCase):
    """Tag gate (#487, invariant 1c): `--tag <ref>` must equal the suite
    version — the one comparison nothing else performs at tag time."""

    def test_matching_tag_passes(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            result = run_script(SCRIPT, "--path", str(root), "--tag", "v3.5.0")
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )

    def test_mismatched_tag_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            result = run_script(SCRIPT, "--path", str(root), "--tag", "v3.6.0")
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            self.assertIn("v3.6.0", result.stdout)
            self.assertIn("3.5.0", result.stdout)

    def test_tag_without_v_prefix_matches(self) -> None:
        """A bare `3.5.0` ref compares equal — the leading `v` is cosmetic."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            result = run_script(SCRIPT, "--path", str(root), "--tag", "3.5.0")
            self.assertEqual(
                result.returncode, 0,
                msg=f"stdout={result.stdout!r} stderr={result.stderr!r}",
            )

    def test_tag_supplied_but_suite_version_missing_fails(self) -> None:
        """The tag gate must NOT silently no-op when .claude/CLAUDE.md has no
        Suite-version line: the whole point of `--tag` is to guarantee the tag
        is right at tag time, so a garbage tag co-occurring with a broken
        CLAUDE.md has to be a non-zero exit (both the suite-missing error AND
        the tag-uncheckable error surface), never a pass."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write_aligned_fixture(root)
            claude_md = root / ".claude" / "CLAUDE.md"
            text = claude_md.read_text(encoding="utf-8")
            text = text.replace(
                "- **Suite version**: 3.5.0 (per CHANGELOG.md)\n", ""
            )
            claude_md.write_text(text, encoding="utf-8")
            result = run_script(SCRIPT, "--path", str(root), "--tag", "v9.9.9")
            self.assertEqual(result.returncode, 1, msg=f"stdout={result.stdout!r}")
            # The tag itself must be named as uncheckable — not just the
            # generic suite-missing error that would fire even without --tag.
            self.assertIn("v9.9.9", result.stdout)


if __name__ == "__main__":
    unittest.main()
