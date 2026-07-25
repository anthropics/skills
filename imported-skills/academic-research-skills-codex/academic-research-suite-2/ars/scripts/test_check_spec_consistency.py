"""Unit tests for check_spec_consistency.py.

Pre-#171, check_spec_consistency.py uses module-level ROOT + ERRORS state.
These tests monkey-patch ROOT into a TemporaryDirectory containing a minimal
fixture README, drive a specific checker directly, and read ERRORS. When
#171 lands the schema-driven manifest, these tests rewrite to call the
manifest runner instead.
"""
from __future__ import annotations

import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from scripts import check_spec_consistency as csc


# Minimal ja-JP README capturing the version-bearing surfaces the lint needs
# to police: badge, release tag link, three release blocks (current + two
# prior so the symmetric structure with check_readme_zh_sections is visible),
# four localized mode headings, four skill-detail headings, and the DOCX line.
JA_README_TEMPLATE = """\
# Academic Research Skills

[![Version](https://img.shields.io/badge/version-v{ver}-blue)](https://github.com/Imbad0202/academic-research-skills/releases/tag/v{ver})

## クイックスタート

#### Deep Research（8 モード）
- outline-only モード
- abstract-only モード
- disclosure モード
- review モード

#### Academic Paper（11 モード）

#### Academic Paper Reviewer（6 モード）
- calibration モード

#### Academic Pipeline（オーケストレーター）

### Deep Research（v2.11.0）
### Academic Paper（v3.2.0）
### Academic Paper Reviewer（v1.10.0）
### Academic Pipeline（v{ver}）

### サポートされる出力フォーマット

- DOCX（利用可能な場合 Pandoc 経由）

## Changelog

### v3.12.0 (2026-06-08) — latest entry
### v3.11.1 (2026-06-06) — prior patch
### v3.11.0 (2026-06-04) — prior patch
### v3.10.0 (2026-06-01) — prior minor
### v3.9.4.2 (2026-05-19) — CI discipline hotfix
### v3.9.4.1 (2026-05-19) — previous hotfix
### v3.9.4 (2026-05-18) — temporal verification
### v3.9.1 (2026-05-18) — client hardening
### v3.9.0 (2026-05-17) — triangulation
### v3.8.0 (2026-05-16) — L3 audit
### v3.7.0 (2026-05-05) — plugin packaging
### v3.6.8 (2026-05-03) — generator-evaluator
### v3.6.7 (2026-04-30) — pattern protection
### v3.6.5 (2026-04-27) — corpus consumer
### v3.6.4 (2026-04-25) — corpus input port
### v3.6.3 (2026-04-23) — passport reset
### v3.6.2 (2026-04-23) — reviewer sprint
### v3.5.1 (2026-04-22) — reading-check probe
### v3.5.0 (2026-04-21) — collaboration depth
### v3.4.0 (2026-04-20) — compliance agent
### v3.3.6 (2026-04-15) — README streamlining
### v3.3.5 (2026-04-15)
### v3.3.4 (2026-04-15) — changelog sync
### v3.3.3 (2026-04-15) — release prep
### v3.3.2 (2026-04-15) — data access levels

## Version Info
- **Suite version**: {ver}
"""


def _write_ja_readme(root: Path, version: str) -> None:
    (root / "README.ja-JP.md").write_text(
        JA_README_TEMPLATE.format(ver=version), encoding="utf-8"
    )


# Minimal ko-KR README capturing the version-bearing surfaces check_readme_ko_sections
# polices: badge, release tag link, the same release-block list as the other locales,
# four localized mode headings ("N개 모드" with ASCII parens — Korean typographic norm
# matching English/ja, NOT the full-width zh form), four skill-detail headings (English
# ASCII-paren form reused verbatim), and the Korean DOCX line.
KO_README_TEMPLATE = """\
# Academic Research Skills

[![Version](https://img.shields.io/badge/version-v{ver}-blue)](https://github.com/Imbad0202/academic-research-skills/releases/tag/v{ver})

## 빠른 시작

#### Deep Research (8개 모드)
- outline-only 모드
- abstract-only 모드
- disclosure 모드
- review 모드

#### Academic Paper (11개 모드)

#### Academic Paper Reviewer (6개 모드)
- calibration 모드

#### Academic Pipeline (오케스트레이터)

### Deep Research (v2.11.0)
### Academic Paper (v3.2.0)
### Academic Paper Reviewer (v1.10.0)
### Academic Pipeline (v{ver})

### 지원되는 출력 형식

- DOCX (가능한 경우 Pandoc 경유)

## 변경 이력

### v3.16.0 (2026-07-12) — current release
### v3.12.0 (2026-06-08) — prior release
### v3.11.1 (2026-06-06) — prior patch
### v3.11.0 (2026-06-04) — prior patch
### v3.10.0 (2026-06-01) — prior minor
### v3.9.4.2 (2026-05-19) — CI discipline hotfix
### v3.9.4.1 (2026-05-19) — previous hotfix
### v3.9.4 (2026-05-18) — temporal verification
### v3.9.1 (2026-05-18) — client hardening
### v3.9.0 (2026-05-17) — triangulation
### v3.8.0 (2026-05-16) — L3 audit
### v3.7.0 (2026-05-05) — plugin packaging
### v3.6.8 (2026-05-03) — generator-evaluator
### v3.6.7 (2026-04-30) — pattern protection
### v3.6.5 (2026-04-27) — corpus consumer
### v3.6.4 (2026-04-25) — corpus input port
### v3.6.3 (2026-04-23) — passport reset
### v3.6.2 (2026-04-23) — reviewer sprint
### v3.5.1 (2026-04-22) — reading-check probe
### v3.5.0 (2026-04-21) — collaboration depth
### v3.4.0 (2026-04-20) — compliance agent
### v3.3.6 (2026-04-15) — README streamlining
### v3.3.5 (2026-04-15)
### v3.3.4 (2026-04-15) — changelog sync
### v3.3.3 (2026-04-15) — release prep
### v3.3.2 (2026-04-15) — data access levels
"""


def _write_ko_readme(root: Path, version: str) -> None:
    (root / "README.ko-KR.md").write_text(
        KO_README_TEMPLATE.format(ver=version), encoding="utf-8"
    )


# Minimal zh-CN README capturing the version-bearing surfaces the lint needs
# to police via ZH_README_CONFIGS[1]: badge, release tag link, the same
# release-block list as zh-TW, four Simplified-Chinese localized mode
# headings, four skill-detail headings, and the Simplified-Chinese DOCX line.
ZH_CN_README_TEMPLATE = """\
# Academic Research Skills

[![Version](https://img.shields.io/badge/version-v{ver}-blue)](https://github.com/Imbad0202/academic-research-skills/releases/tag/v{ver})

#### Deep Research（深度研究，8 种模式）
- review mode

#### Academic Paper（学术论文撰写，11 种模式）
- outline-only mode
- abstract-only mode
- disclosure mode

#### Academic Paper Reviewer（论文审查，6 种模式）
- calibration mode

#### Academic Pipeline（全流程调度器）

### Deep Research (v2.11.0)
### Academic Paper (v3.2.0)
### Academic Paper Reviewer (v1.10.0)
### Academic Pipeline (v{ver})

### 支持的输出格式

- DOCX（Pandoc 可用时）

## 更新纪录

### v3.12.0（2026-06-08）— latest entry
### v3.11.1（2026-06-06）— prior patch
### v3.11.0（2026-06-04）— prior patch
### v3.10.0（2026-06-01）— prior minor
### v3.9.4.2（2026-05-19）— CI discipline hotfix
### v3.9.4.1（2026-05-19）— previous hotfix
### v3.9.4（2026-05-18）— temporal verification
### v3.9.1（2026-05-18）— client hardening
### v3.9.0（2026-05-17）— triangulation
### v3.8.0（2026-05-16）— L3 audit
### v3.7.0（2026-05-05）— plugin packaging
### v3.6.8（2026-05-03）— generator-evaluator
### v3.6.7（2026-04-30）— pattern protection
### v3.6.5（2026-04-27）— corpus consumer
### v3.6.4（2026-04-25）— corpus input port
### v3.6.3（2026-04-23）— passport reset
### v3.6.2（2026-04-23）— reviewer sprint
### v3.5.1（2026-04-22）— reading-check probe
### v3.5.0（2026-04-21）— collaboration depth
### v3.4.0（2026-04-20）— compliance agent
### v3.3.6 (2026-04-15) — README streamlining
### v3.3.5 (2026-04-15)
### v3.3.4 (2026-04-15) — changelog sync
### v3.3.3 (2026-04-15) — release prep
### v3.3.2 (2026-04-15) — data access levels
"""


def _write_zh_cn_readme(root: Path, version: str) -> None:
    (root / "README.zh-CN.md").write_text(
        ZH_CN_README_TEMPLATE.format(ver=version), encoding="utf-8"
    )


# zh-TW fixture matching ZH_README_CONFIGS[0]. check_readme_zh_sections
# iterates BOTH configs, so to test the zh-CN branch in isolation we still
# need a passing zh-TW companion (or vice versa). The minimal zh-TW fixture
# below uses the same shape with Traditional-Chinese localized strings.
ZH_TW_README_TEMPLATE = """\
# Academic Research Skills

[![Version](https://img.shields.io/badge/version-v{ver}-blue)](https://github.com/Imbad0202/academic-research-skills/releases/tag/v{ver})

#### Deep Research（深度研究，8 種模式）
- review mode

#### Academic Paper（學術論文撰寫，11 種模式）
- outline-only mode
- abstract-only mode
- disclosure mode

#### Academic Paper Reviewer（論文審查，6 種模式）
- calibration mode

#### Academic Pipeline（全流程調度器）

### Deep Research (v2.11.0)
### Academic Paper (v3.2.0)
### Academic Paper Reviewer (v1.10.0)
### Academic Pipeline (v{ver})

### 支援的輸出格式

- DOCX（Pandoc 可用時）

## 更新紀錄

### v3.12.0（2026-06-08）— latest entry
### v3.11.1（2026-06-06）— prior patch
### v3.11.0（2026-06-04）— prior patch
### v3.10.0（2026-06-01）— prior minor
### v3.9.4.2（2026-05-19）— CI discipline hotfix
### v3.9.4.1（2026-05-19）— previous hotfix
### v3.9.4（2026-05-18）— temporal verification
### v3.9.1（2026-05-18）— client hardening
### v3.9.0（2026-05-17）— triangulation
### v3.8.0（2026-05-16）— L3 audit
### v3.7.0（2026-05-05）— plugin packaging
### v3.6.8（2026-05-03）— generator-evaluator
### v3.6.7（2026-04-30）— pattern protection
### v3.6.5（2026-04-27）— corpus consumer
### v3.6.4（2026-04-25）— corpus input port
### v3.6.3（2026-04-23）— passport reset
### v3.6.2（2026-04-23）— reviewer sprint
### v3.5.1（2026-04-22）— reading-check probe
### v3.5.0（2026-04-21）— collaboration depth
### v3.4.0（2026-04-20）— compliance agent
### v3.3.6 (2026-04-15) — README streamlining
### v3.3.5 (2026-04-15)
### v3.3.4 (2026-04-15) — changelog sync
### v3.3.3 (2026-04-15) — release prep
### v3.3.2 (2026-04-15) — data access levels
"""


def _write_zh_tw_readme(root: Path, version: str) -> None:
    (root / "README.zh-TW.md").write_text(
        ZH_TW_README_TEMPLATE.format(ver=version), encoding="utf-8"
    )


class TestReadmeJaSections(unittest.TestCase):
    def setUp(self) -> None:
        # check_spec_consistency uses module-level ROOT and ERRORS. Reset and
        # restore around each test so state does not leak between cases.
        self._orig_root = csc.ROOT
        self._orig_errors = list(csc.ERRORS)
        csc.ERRORS.clear()

    def tearDown(self) -> None:
        csc.ROOT = self._orig_root
        csc.ERRORS.clear()
        csc.ERRORS.extend(self._orig_errors)

    def test_aligned_ja_readme_passes(self) -> None:
        """A README.ja-JP.md whose badge / tag link / release headings all
        agree with the suite version v3.9.4.2 must pass without errors."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_ja_readme(root, version="3.16.0")

            csc.check_readme_ja_sections()

            self.assertEqual(
                csc.ERRORS, [],
                msg=f"unexpected errors on aligned fixture: {csc.ERRORS!r}",
            )

    def test_stale_ja_badge_fails(self) -> None:
        """Regression for #170: if README.ja-JP.md keeps a stale v3.9.4.0
        badge while CHANGELOG has moved to v3.9.4.2, the lint must surface
        the drift instead of silently passing (pre-fix behavior: this file
        was outside the lint's needle list and the drift never surfaced)."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            # Write the "current" v3.9.4.2 release block but downgrade only
            # the badge and tag link to v3.9.4.0. This is the realistic shape
            # of drift when one place gets forgotten during a release.
            stale = JA_README_TEMPLATE.format(ver="3.16.0").replace(
                "version-v3.16.0-blue", "version-v3.9.4.0-blue"
            ).replace(
                "releases/tag/v3.16.0", "releases/tag/v3.9.4.0"
            )
            (root / "README.ja-JP.md").write_text(stale, encoding="utf-8")

            csc.check_readme_ja_sections()

            self.assertTrue(
                any("README.ja-JP.md" in e and "v3.16.0" in e for e in csc.ERRORS),
                msg=f"expected ja-JP drift error in: {csc.ERRORS!r}",
            )


class TestReadmeKoSections(unittest.TestCase):
    def setUp(self) -> None:
        # check_spec_consistency uses module-level ROOT and ERRORS. Reset and
        # restore around each test so state does not leak between cases.
        self._orig_root = csc.ROOT
        self._orig_errors = list(csc.ERRORS)
        csc.ERRORS.clear()

    def tearDown(self) -> None:
        csc.ROOT = self._orig_root
        csc.ERRORS.clear()
        csc.ERRORS.extend(self._orig_errors)

    def test_aligned_ko_readme_passes(self) -> None:
        """A README.ko-KR.md whose badge / tag link / release headings / Korean
        mode + skill headings all agree with the suite version must pass."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_ko_readme(root, version="3.16.0")

            csc.check_readme_ko_sections()

            self.assertEqual(
                csc.ERRORS, [],
                msg=f"unexpected errors on aligned ko fixture: {csc.ERRORS!r}",
            )

    def test_stale_ko_badge_fails(self) -> None:
        """Symmetric to the ja drift regression: a stale badge / tag link on
        README.ko-KR.md must surface the drift rather than silently passing."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            stale = KO_README_TEMPLATE.format(ver="3.16.0").replace(
                "version-v3.16.0-blue", "version-v3.9.4.0-blue"
            ).replace(
                "releases/tag/v3.16.0", "releases/tag/v3.9.4.0"
            )
            (root / "README.ko-KR.md").write_text(stale, encoding="utf-8")

            csc.check_readme_ko_sections()

            self.assertTrue(
                any("README.ko-KR.md" in e and "v3.16.0" in e for e in csc.ERRORS),
                msg=f"expected ko-KR drift error in: {csc.ERRORS!r}",
            )

    def test_missing_korean_mode_heading_fails(self) -> None:
        """If a localized mode heading is dropped (e.g. the "N개 모드" form is
        accidentally written in the English "(8 modes)" shape), the lint must
        catch it — proving the heading checks are load-bearing, not vacuous."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            broken = KO_README_TEMPLATE.format(ver="3.16.0").replace(
                "#### Deep Research (8개 모드)", "#### Deep Research (8 modes)"
            )
            (root / "README.ko-KR.md").write_text(broken, encoding="utf-8")

            csc.check_readme_ko_sections()

            self.assertTrue(
                any("README.ko-KR.md" in e and "8개 모드" in e for e in csc.ERRORS),
                msg=f"expected missing-heading error in: {csc.ERRORS!r}",
            )

    def test_full_width_korean_changelog_parentheses_fail(self) -> None:
        """Korean changelog headings use ASCII parentheses, not full-width forms."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            broken = KO_README_TEMPLATE.format(ver="3.16.0").replace(
                "### v3.16.0 (2026-07-12)",
                "### v3.16.0（2026-07-12）",
            )
            (root / "README.ko-KR.md").write_text(broken, encoding="utf-8")

            csc.check_readme_ko_sections()

            self.assertTrue(
                any(
                    "README.ko-KR.md" in e
                    and "### v3.16.0 (2026-07-12)" in e
                    for e in csc.ERRORS
                ),
                msg=f"expected Korean parenthesis-style error in: {csc.ERRORS!r}",
            )


class TestReadmeZhSections(unittest.TestCase):
    """Coverage for the ZH_README_CONFIGS tuple branch added when zh-CN
    joined zh-TW under check_readme_zh_sections. check_readme_zh_sections
    iterates both configs, so both fixtures must exist on every test path."""

    def setUp(self) -> None:
        self._orig_root = csc.ROOT
        self._orig_errors = list(csc.ERRORS)
        csc.ERRORS.clear()

    def tearDown(self) -> None:
        csc.ROOT = self._orig_root
        csc.ERRORS.clear()
        csc.ERRORS.extend(self._orig_errors)

    def test_aligned_zh_cn_readme_passes(self) -> None:
        """Both zh-TW and zh-CN fixtures aligned to v3.9.4.2 produce no
        lint errors. Locks the new ZH_README_CONFIGS[1] branch."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_zh_tw_readme(root, version="3.16.0")
            _write_zh_cn_readme(root, version="3.16.0")

            csc.check_readme_zh_sections()

            self.assertEqual(
                csc.ERRORS, [],
                msg=f"unexpected errors on aligned zh fixtures: {csc.ERRORS!r}",
            )

    def test_stale_zh_cn_badge_fails(self) -> None:
        """Regression symmetric with #170 ja-JP: if README.zh-CN.md keeps
        a stale v3.9.4.0 badge while the rest of the file moved to v3.9.4.2,
        the lint must surface the drift on the zh-CN branch specifically."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_zh_tw_readme(root, version="3.16.0")
            stale = ZH_CN_README_TEMPLATE.format(ver="3.16.0").replace(
                "version-v3.16.0-blue", "version-v3.9.4.0-blue"
            ).replace(
                "releases/tag/v3.16.0", "releases/tag/v3.9.4.0"
            )
            (root / "README.zh-CN.md").write_text(stale, encoding="utf-8")

            csc.check_readme_zh_sections()

            self.assertTrue(
                any("README.zh-CN.md" in e and "v3.16.0" in e for e in csc.ERRORS),
                msg=f"expected zh-CN drift error in: {csc.ERRORS!r}",
            )


# Minimal docs/ARCHITECTURE.md fixture carrying the THREE marker kinds the invariant-4 check (#345)
# must distinguish: current-component markers (mermaid node + component/stage rows, which MUST equal
# the suite version), a feature-history timeline marker (`vX.Y.Z : <feature>`, which must NOT be
# policed), and a prose mention of `academic-pipeline vX.Y.Z` (provenance narrative, which must also
# NOT be policed — it is excluded by the table-row anchor). `{comp}` = current-component version;
# `{hist}` = timeline version; `{prose}` = the version named in the narrative provenance line.
ARCHITECTURE_TEMPLATE = """\
# Architecture

```mermaid
flowchart TD
    Pipeline[academic-pipeline<br/>orchestrator<br/>v{comp}<br/>Agent Team: 5]
```

| Stage | Gate | ... |
|-------|------|-----|
| **2.5 INTEGRITY** | `academic-pipeline` v{comp} (gate) | VERIFIED_ONLY |
| **6. PROCESS SUMMARY** | `academic-pipeline` v{comp} | VERIFIED_ONLY |

| Component | Role |
|-----------|------|
| `academic-pipeline` v{comp} | orchestrator (delegates to sub-skill modes) |

The `academic-pipeline` v{prose} release first introduced the integrity gate (narrative provenance).

```mermaid
timeline
    title ARS evolution timeline
    v{hist} : deterministic citation verification gate (#182)
```
"""


def _write_architecture_fixture(
    root: Path, *, suite: str, comp: str, hist: str, prose: str | None = None
) -> None:
    """Write `.claude/CLAUDE.md` (suite version source) + a docs/ARCHITECTURE.md fixture.

    `prose` defaults to the suite version so the narrative line is innocuous unless a test
    deliberately sets it to a stale version to assert the prose mention is not policed.
    """
    (root / ".claude").mkdir(parents=True, exist_ok=True)
    (root / ".claude" / "CLAUDE.md").write_text(
        f"# ARS\n\n- **Suite version**: {suite} (per CHANGELOG.md)\n", encoding="utf-8"
    )
    (root / "docs").mkdir(parents=True, exist_ok=True)
    (root / "docs" / "ARCHITECTURE.md").write_text(
        ARCHITECTURE_TEMPLATE.format(comp=comp, hist=hist, prose=prose or suite),
        encoding="utf-8",
    )


class TestArchitectureComponentVersion(unittest.TestCase):
    """#345: invariant-4 lint for docs/ARCHITECTURE.md current-component version markers."""

    def setUp(self) -> None:
        self._orig_root = csc.ROOT
        self._orig_errors = list(csc.ERRORS)
        csc.ERRORS.clear()

    def tearDown(self) -> None:
        csc.ROOT = self._orig_root
        csc.ERRORS.clear()
        csc.ERRORS.extend(self._orig_errors)

    def test_aligned_passes(self) -> None:
        """All component markers at the suite version → no errors (timeline at an older version
        is fine — it records history)."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_architecture_fixture(root, suite="3.11.1", comp="3.11.1", hist="3.11.0")

            csc.check_architecture_component_version()

            self.assertEqual(
                csc.ERRORS, [], msg=f"unexpected errors on aligned fixture: {csc.ERRORS!r}"
            )

    def test_stale_component_marker_fails(self) -> None:
        """A current-component marker left at the prior version (the exact #343/#344 drift) must
        fail — both the mermaid node and the rows carry the stale version here."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_architecture_fixture(root, suite="3.11.1", comp="3.11.0", hist="3.11.0")

            csc.check_architecture_component_version()

            self.assertTrue(
                any("ARCHITECTURE.md" in e and "3.11.0" in e and "3.11.1" in e for e in csc.ERRORS),
                msg=f"expected stale-component drift error in: {csc.ERRORS!r}",
            )

    def test_stale_timeline_marker_does_not_fail(self) -> None:
        """The critical distinction: a timeline `vX.Y.Z : <feature>` node at a DIFFERENT version
        from the suite must NOT fail — it records which version shipped a feature, and a
        naive `v3.x` scan would wrongly flag it. Component markers are aligned here."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            # Component markers all at the suite version; only the timeline records an old version.
            _write_architecture_fixture(root, suite="3.11.1", comp="3.11.1", hist="3.9.4")

            csc.check_architecture_component_version()

            self.assertEqual(
                csc.ERRORS, [],
                msg=f"timeline marker must not be policed, but got: {csc.ERRORS!r}",
            )

    def test_missing_component_marker_fails(self) -> None:
        """If the component markers vanish entirely (e.g. a refactor removes them), the check must
        surface that rather than silently passing on an empty match."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            (root / ".claude").mkdir(parents=True, exist_ok=True)
            (root / ".claude" / "CLAUDE.md").write_text(
                "- **Suite version**: 3.11.1 (per CHANGELOG.md)\n", encoding="utf-8"
            )
            (root / "docs").mkdir(parents=True, exist_ok=True)
            (root / "docs" / "ARCHITECTURE.md").write_text(
                "# Architecture\n\nNo component markers here.\n", encoding="utf-8"
            )

            csc.check_architecture_component_version()

            self.assertTrue(
                any("no mermaid" in e or "no `academic-pipeline" in e for e in csc.ERRORS),
                msg=f"expected missing-marker error in: {csc.ERRORS!r}",
            )

    def test_four_component_aligned_passes(self) -> None:
        """#352 P2: the repo's own grammar ships 4-component versions (v3.9.4.2). A suite and
        component markers both at a 4-component version must pass — the version regex must capture
        the FULL token, not truncate to three components."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_architecture_fixture(root, suite="3.9.4.2", comp="3.9.4.2", hist="3.9.4")

            csc.check_architecture_component_version()

            self.assertEqual(
                csc.ERRORS, [],
                msg=f"unexpected errors on aligned 4-component fixture: {csc.ERRORS!r}",
            )

    def test_four_component_marker_against_three_component_suite_fails(self) -> None:
        """#352 P2 (the silent-pass this fix closes): suite is the 3-component `3.9.4` but a
        component marker carries the 4-component `3.9.4.2`. A truncating `\\d+\\.\\d+\\.\\d+`
        would capture `3.9.4` from the marker and falsely pass (3.9.4 == 3.9.4). The full-token
        capture must instead see `3.9.4.2` and fail it against the suite."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_architecture_fixture(root, suite="3.9.4", comp="3.9.4.2", hist="3.9.4")

            csc.check_architecture_component_version()

            # The error must name the FULL 4-component marker as != the 3-component suite. Asserting
            # on `!= suite v3.9.4` (not just substring `3.9.4`, which is contained in `3.9.4.2`)
            # proves the captured marker was the full `3.9.4.2`, i.e. the truncation was closed.
            self.assertTrue(
                any("v3.9.4.2" in e and "!= suite v3.9.4 " in e for e in csc.ERRORS),
                msg=f"expected 4-vs-3-component drift error in: {csc.ERRORS!r}",
            )

    def test_prose_provenance_mention_does_not_fail(self) -> None:
        """#352 P3: a narrative line naming `academic-pipeline v<old>` (feature provenance) must
        NOT be policed against the suite version — only markdown table-row component cells are.
        Component markers + timeline are aligned/innocuous; only the prose line is stale."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_architecture_fixture(
                root, suite="3.11.1", comp="3.11.1", hist="3.9.4", prose="3.9.4"
            )

            csc.check_architecture_component_version()

            self.assertEqual(
                csc.ERRORS, [],
                msg=f"prose provenance mention must not be policed, but got: {csc.ERRORS!r}",
            )


# --- #377: SKILL.md frontmatter↔table consistency (all 4) + suite-skill date sanity ---

# Minimal SKILL.md carrying the version-bearing surfaces the #377 check polices: a
# `metadata:` frontmatter block with `version` / `last_updated`, and a Version-Info table
# with `| Skill Version |` / `| Last Updated |` rows. Mirrors the real four SKILL.md shape.
SKILL_TEMPLATE = """\
---
name: {name}
metadata:
  version: "{fm_ver}"
  last_updated: "{fm_date}"
---

# {name}

Body.

## Version Info

| Field | Value |
|-------|-------|
| Skill Version | {tbl_ver} |
| Last Updated | {tbl_date} |
"""

# The four SKILL.md paths the generalized check must cover, with their real independent
# versions/dates. `academic-pipeline` tracks the suite; the other three move independently.
_SKILL_FIXTURES = {
    "academic-pipeline": ("3.12.0", "2026-06-08"),
    "academic-paper": ("3.2.0", "2026-06-01"),
    "academic-paper-reviewer": ("1.10.0", "2026-06-01"),
    "deep-research": ("2.9.4", "2026-05-18"),
}


def _write_skill_fixtures(root: Path, overrides: dict | None = None) -> None:
    """Write all four SKILL.md with frontmatter == table by default. `overrides` maps a
    skill dir to a partial dict of {fm_ver, fm_date, tbl_ver, tbl_date} to introduce drift."""
    overrides = overrides or {}
    for skill, (ver, date) in _SKILL_FIXTURES.items():
        fields = {"fm_ver": ver, "fm_date": date, "tbl_ver": ver, "tbl_date": date}
        fields.update(overrides.get(skill, {}))
        (root / skill).mkdir(parents=True, exist_ok=True)
        (root / skill / "SKILL.md").write_text(
            SKILL_TEMPLATE.format(name=skill, **fields), encoding="utf-8"
        )


class TestSkillVersionTableConsistency(unittest.TestCase):
    """#377(a): frontmatter version/last_updated ↔ Version-Info table for ALL FOUR SKILL.md
    (pre-#377 only academic-paper-reviewer was checked)."""

    def setUp(self) -> None:
        self._orig_root = csc.ROOT
        self._orig_errors = list(csc.ERRORS)
        csc.ERRORS.clear()

    def tearDown(self) -> None:
        csc.ROOT = self._orig_root
        csc.ERRORS.clear()
        csc.ERRORS.extend(self._orig_errors)

    def test_all_four_aligned_passes(self) -> None:
        """All four SKILL.md with frontmatter matching their table → no errors."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_skill_fixtures(root)

            csc.check_skill_version_blocks()

            self.assertEqual(
                csc.ERRORS, [], msg=f"unexpected errors on aligned fixtures: {csc.ERRORS!r}"
            )

    def test_table_date_drift_in_non_reviewer_skill_fails(self) -> None:
        """The exact #377 root cause: a SKILL whose frontmatter date is bumped but whose table
        date is left stale must fail — and crucially for a skill OTHER than reviewer (which is
        the only one the pre-#377 check covered)."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_skill_fixtures(
                root, overrides={"academic-pipeline": {"tbl_date": "2026-06-01"}}
            )

            csc.check_skill_version_blocks()

            self.assertTrue(
                any(
                    "academic-pipeline/SKILL.md" in e and "2026-06-08" in e and "2026-06-01" in e
                    for e in csc.ERRORS
                ),
                msg=f"expected frontmatter↔table date drift error in: {csc.ERRORS!r}",
            )

    def test_table_version_drift_fails(self) -> None:
        """A version (not date) drift between frontmatter and table also fails — for a third
        skill (deep-research) to prove the check is not reviewer-specific."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_skill_fixtures(
                root, overrides={"deep-research": {"tbl_ver": "2.9.3"}}
            )

            csc.check_skill_version_blocks()

            self.assertTrue(
                any(
                    "deep-research/SKILL.md" in e and "2.9.4" in e and "2.9.3" in e
                    for e in csc.ERRORS
                ),
                msg=f"expected frontmatter↔table version drift error in: {csc.ERRORS!r}",
            )

    def test_missing_table_rows_fails(self) -> None:
        """A SKILL.md that loses its Version-Info table rows must surface rather than silently
        pass on an empty match."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_skill_fixtures(root)
            (root / "academic-paper" / "SKILL.md").write_text(
                '---\nname: academic-paper\nmetadata:\n  version: "3.2.0"\n'
                '  last_updated: "2026-06-01"\n---\n\nNo version table here.\n',
                encoding="utf-8",
            )

            csc.check_skill_version_blocks()

            self.assertTrue(
                any("academic-paper/SKILL.md" in e and "Version Info" in e for e in csc.ERRORS),
                msg=f"expected missing-table-rows error in: {csc.ERRORS!r}",
            )


# Minimal CHANGELOG whose latest entry date is the parameter; the suite-date-sanity check
# compares academic-pipeline/SKILL.md last_updated against this. Two prior entries so the
# "latest" selection (first `## [X.Y.Z]` after [Unreleased]) is exercised, not just sole-entry.
CHANGELOG_TEMPLATE = """\
# Changelog

## [Unreleased]

## [{latest_ver}] - {latest_date} — latest real entry

## [3.11.1] - 2026-06-06 — prior patch

## [3.11.0] - 2026-06-04 — prior minor
"""


def _write_date_sanity_fixtures(
    root: Path, *, changelog_date: str, pipeline_date: str, changelog_ver: str = "3.12.0"
) -> None:
    """Write a CHANGELOG with a known latest-entry date + four SKILL.md where only
    academic-pipeline's last_updated is the variable under test."""
    (root / "CHANGELOG.md").write_text(
        CHANGELOG_TEMPLATE.format(latest_ver=changelog_ver, latest_date=changelog_date),
        encoding="utf-8",
    )
    _write_skill_fixtures(
        root,
        overrides={
            "academic-pipeline": {"fm_date": pipeline_date, "tbl_date": pipeline_date}
        },
    )


class TestSuiteSkillDateSanity(unittest.TestCase):
    """#377(b): academic-pipeline/SKILL.md last_updated must be >= the latest CHANGELOG entry
    date. The other three SKILL.md version independently and are NOT date-policed here."""

    def setUp(self) -> None:
        self._orig_root = csc.ROOT
        self._orig_errors = list(csc.ERRORS)
        csc.ERRORS.clear()

    def tearDown(self) -> None:
        csc.ROOT = self._orig_root
        csc.ERRORS.clear()
        csc.ERRORS.extend(self._orig_errors)

    def test_pipeline_date_equal_to_changelog_passes(self) -> None:
        """last_updated == latest CHANGELOG date → fine (the normal aligned-release case)."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_date_sanity_fixtures(
                root, changelog_date="2026-06-08", pipeline_date="2026-06-08"
            )

            csc.check_suite_skill_date_sanity()

            self.assertEqual(
                csc.ERRORS, [], msg=f"unexpected errors on aligned date: {csc.ERRORS!r}"
            )

    def test_pipeline_date_after_changelog_passes(self) -> None:
        """last_updated strictly AFTER the latest CHANGELOG date is allowed — a post-release
        doc touch legitimately advances the date past the release entry."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_date_sanity_fixtures(
                root, changelog_date="2026-06-08", pipeline_date="2026-06-10"
            )

            csc.check_suite_skill_date_sanity()

            self.assertEqual(
                csc.ERRORS, [], msg=f"a later last_updated must pass, got: {csc.ERRORS!r}"
            )

    def test_pipeline_date_before_changelog_fails(self) -> None:
        """The exact v3.12.0 drift: suite version bumped, last_updated left at the prior release
        date (earlier than the latest CHANGELOG entry) → must fail."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_date_sanity_fixtures(
                root, changelog_date="2026-06-08", pipeline_date="2026-06-01"
            )

            csc.check_suite_skill_date_sanity()

            self.assertTrue(
                any(
                    "academic-pipeline/SKILL.md" in e
                    and "2026-06-01" in e
                    and "2026-06-08" in e
                    for e in csc.ERRORS
                ),
                msg=f"expected stale-suite-date error in: {csc.ERRORS!r}",
            )

    def test_date_check_is_bound_to_suite_path_only(self) -> None:
        """Out-of-scope guard (#377): the date check polices ONLY `_SUITE_SKILL_PATH`. To prove
        this is genuine scoping and not a vacuous pass, the test demonstrates that the SAME early
        date is ignored when carried by an independent skill but flagged when carried by whatever
        path `_SUITE_SKILL_PATH` names — i.e. repointing the constant repoints the policing.

        Fixture: pipeline date is current (2026-06-08, == CHANGELOG); academic-paper carries an
        early date (2026-06-01 < CHANGELOG). With the real constant the early academic-paper date
        is NOT flagged; after repointing the constant AT academic-paper, that exact same early
        date IS flagged. If the check ever fanned out across all four skills, the first assertion
        would already fail."""
        orig_suite_path = csc._SUITE_SKILL_PATH
        try:
            with TemporaryDirectory() as tmp:
                root = Path(tmp)
                csc.ROOT = root
                _write_date_sanity_fixtures(
                    root, changelog_date="2026-06-08", pipeline_date="2026-06-08"
                )
                # academic-paper keeps its default early date (2026-06-01) from _write_skill_fixtures.

                # Real constant → only pipeline policed; academic-paper's early date is ignored.
                csc.check_suite_skill_date_sanity()
                self.assertEqual(
                    csc.ERRORS, [],
                    msg=f"independent-skill early date must not be policed, got: {csc.ERRORS!r}",
                )

                # Repoint the constant at academic-paper → its early date is now the policed one.
                csc.ERRORS.clear()
                csc._SUITE_SKILL_PATH = "academic-paper/SKILL.md"
                csc.check_suite_skill_date_sanity()
                self.assertTrue(
                    any(
                        "academic-paper/SKILL.md" in e and "2026-06-01" in e and "2026-06-08" in e
                        for e in csc.ERRORS
                    ),
                    msg=f"repointed suite path must police academic-paper's early date: {csc.ERRORS!r}",
                )
        finally:
            csc._SUITE_SKILL_PATH = orig_suite_path

    def test_malformed_suite_skill_does_not_double_report(self) -> None:
        """When the suite SKILL.md is unparseable, check_skill_version_blocks() already records the
        error; check_suite_skill_date_sanity() must NOT re-report the same root cause from its own
        re-parse. Drives both checks in order (as main() does) and asserts a single pipeline error."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            csc.ROOT = root
            _write_date_sanity_fixtures(
                root, changelog_date="2026-06-08", pipeline_date="2026-06-08"
            )
            # Strip the suite SKILL's Version-Info table rows so it fails to parse.
            pipeline_skill = root / "academic-pipeline" / "SKILL.md"
            text = pipeline_skill.read_text(encoding="utf-8")
            pipeline_skill.write_text(
                text.replace("| Skill Version | 3.12.0 |", "").replace(
                    "| Last Updated | 2026-06-08 |", ""
                ),
                encoding="utf-8",
            )

            csc.check_skill_version_blocks()
            csc.check_suite_skill_date_sanity()

            pipeline_errors = [e for e in csc.ERRORS if "academic-pipeline/SKILL.md" in e]
            self.assertEqual(
                len(pipeline_errors), 1,
                msg=f"expected exactly one pipeline error, got {len(pipeline_errors)}: {pipeline_errors!r}",
            )


class RebuttalAuditGuardTest(unittest.TestCase):
    """check_rebuttal_audit_guard() must enforce the integrity-boundary language
    in the academic-paper Rebuttal-Audit Mode section. Mutation tests prove the
    guard actually fails when the suppression language is dropped — otherwise the
    check would be a vacuous pass that lets the false-certification risk back in."""

    _GOOD = (
        "## Rebuttal-Audit Mode\n\n"
        "Advisory QA of an existing rebuttal draft.\n\n"
        "**IRON RULE:** standalone, so it MUST NOT emit a Schema 11 ledger, "
        "MUST NOT write the Material Passport, and MUST NOT mark ready_to_submit.\n\n"
        "## Next Section\n"
    )

    def _run_guard_with(self, skill_text: str) -> list:
        orig_read = csc.read
        csc.ERRORS.clear()
        try:
            csc.read = lambda rel: skill_text if rel == "academic-paper/SKILL.md" else orig_read(rel)
            csc.check_rebuttal_audit_guard()
            return list(csc.ERRORS)
        finally:
            csc.read = orig_read
            csc.ERRORS.clear()

    def test_guard_passes_with_full_suppression_language(self) -> None:
        self.assertEqual(self._run_guard_with(self._GOOD), [])

    def test_guard_fails_when_section_missing(self) -> None:
        errs = self._run_guard_with("## Some Other Mode\n\nno rebuttal section here\n")
        self.assertTrue(any("missing" in e and "Rebuttal-Audit" in e for e in errs), errs)

    def test_guard_fails_when_schema11_suppression_dropped(self) -> None:
        mutated = self._GOOD.replace("Schema 11", "the tracker")
        errs = self._run_guard_with(mutated)
        self.assertTrue(any("Schema 11" in e for e in errs), errs)

    def test_guard_fails_when_must_not_dropped(self) -> None:
        mutated = self._GOOD.replace("MUST NOT", "should avoid")
        errs = self._run_guard_with(mutated)
        self.assertTrue(any("MUST NOT" in e for e in errs), errs)


if __name__ == "__main__":
    unittest.main()
