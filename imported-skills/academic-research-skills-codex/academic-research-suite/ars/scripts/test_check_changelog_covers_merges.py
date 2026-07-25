"""Unit tests for check_changelog_covers_merges.py."""
from __future__ import annotations

import subprocess
import textwrap
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script

SCRIPT = Path(__file__).resolve().parent / "check_changelog_covers_merges.py"
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_changelog_covers_merges import (  # noqa: E402
    all_refs,
    audit,
    extract_coverage_text,
    extract_unreleased,
    is_covered,
    is_exempt,
    pr_number,
    Uncovered,
)


class PrNumberTest(unittest.TestCase):
    def test_trailing_pr_is_identity(self):
        self.assertEqual(pr_number("Harden title-fallback (#432)"), 432)

    def test_mid_subject_ref_ignored_when_trailing_present(self):
        # #89 is a tracking issue mid-subject; #429 is the PR (trailing).
        self.assertEqual(
            pr_number("route integrity-FAIL (#89 Item 8) (#429)"), 429
        )

    def test_no_trailing_pr_returns_none(self):
        self.assertIsNone(pr_number("Harden title-fallback, no suffix"))

    def test_mid_ref_only_is_not_identity(self):
        # a number that is NOT a trailing (#N) does not count as the PR
        self.assertIsNone(pr_number("fixes (#89 Item 8) but no PR suffix"))

    def test_bare_hash_without_parens_is_none(self):
        # a #N without the surrounding parens is not a PR identity
        self.assertIsNone(pr_number("fixes bug #42"))


class AllRefsTest(unittest.TestCase):
    """§0.1: all_refs is the COVERAGE namespace — every #N in the subject."""

    def test_collects_issue_and_pr(self):
        # mid-subject issue ref + trailing PR are both refs
        self.assertEqual(
            all_refs("feat(socratic): probes (#393) (#400)"), [393, 400]
        )

    def test_umbrella_and_pr(self):
        self.assertEqual(
            all_refs("fix: route correction (#89 Item 8) (#429)"), [89, 429]
        )

    def test_single_trailing(self):
        self.assertEqual(all_refs("Harden title-fallback (#432)"), [432])

    def test_no_refs_is_empty(self):
        self.assertEqual(all_refs("Harden thing with no ref"), [])

    def test_bare_hash_counts_as_ref(self):
        # all_refs is liberal (any #N); the # is still required
        self.assertEqual(all_refs("fixes bug #42 and #43"), [42, 43])
        self.assertEqual(all_refs("no hash here 42"), [])


class IsExemptTest(unittest.TestCase):
    def test_exempt_types(self):
        for subj in [
            "chore: bump deps (#1)",
            "test: add pin (#2)",
            "ci: tweak workflow (#3)",
            "build: package (#4)",
            "ci(scope): scoped ci (#5)",  # scope-tolerant
        ]:
            self.assertTrue(is_exempt(subj), subj)

    def test_exempt_internal_docs_scopes(self):
        self.assertTrue(is_exempt("docs(design): spec (#6)"))
        self.assertTrue(is_exempt("docs(superpowers): plan (#7)"))

    def test_exempt_release_mechanics_docs_scope(self):
        # docs(release): the once-per-release alignment/promotion commit IS the
        # changelog being written — it cannot cite itself (§0.2).
        self.assertTrue(is_exempt("docs(release): align all doc surfaces for v3.14.0 (#481)"))

    def test_i18n_docs_required(self):
        # Translation changes are user-facing docs like any other (codex P2):
        # exempting docs(i18n) would let them slip through undocumented.
        self.assertFalse(is_exempt("docs(i18n): apply review P3s (#482)"))

    def test_required_prefixes(self):
        for subj in [
            "feat: thing (#8)",
            "fix: bug (#9)",
            "docs: user-facing (#10)",          # bare docs REQUIRED
            "docs(contributing): guide (#11)",  # other docs scope REQUIRED
            "refactor: cleanup (#12)",
            "perf: speed (#13)",
            "Harden title-fallback (#14)",      # no-prefix REQUIRED
        ]:
            self.assertFalse(is_exempt(subj), subj)

    def test_breaking_marker_and_case_sensitivity(self):
        # breaking-change "!" marker must not disturb scope parsing
        self.assertTrue(is_exempt("docs(design)!: breaking spec (#15)"))
        self.assertTrue(is_exempt("chore(deps)!: bump (#16)"))
        # type match is case-sensitive: capitalized prefixes are REQUIRED
        self.assertFalse(is_exempt("Chore: capitalized (#17)"))
        self.assertFalse(is_exempt('Revert "feat: x" (#18)'))


class IsCoveredTest(unittest.TestCase):
    UNRELEASED = "- **Thing (#432).** did a thing\n- another (#89 Item 7)\n"

    def test_covered_exact(self):
        self.assertTrue(is_covered(432, self.UNRELEASED))

    def test_token_boundary_no_substring_match(self):
        # #42 must NOT be "covered" by #432 in the text
        self.assertFalse(is_covered(42, self.UNRELEASED))

    def test_uncovered(self):
        self.assertFalse(is_covered(999, self.UNRELEASED))

    def test_requires_hash_prefix(self):
        # a bare "432" (no #) in prose must not count
        self.assertFalse(is_covered(432, "the year was 432 AD\n"))


class AuditTest(unittest.TestCase):
    def test_required_covered_passes(self):
        subjects = ["feat: thing (#432)"]
        unreleased = "- thing (#432)\n"
        self.assertEqual(audit(subjects, unreleased), [])

    def test_required_uncovered_fails(self):
        subjects = ["feat: thing (#999)"]
        unreleased = "- something else (#1)\n"
        result = audit(subjects, unreleased)
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].pr, 999)
        self.assertEqual(result[0].reason, "not covered")

    def test_exempt_skipped_even_if_uncovered(self):
        subjects = ["chore: x (#7)", "test: y (#8)"]
        self.assertEqual(audit(subjects, ""), [])

    def test_no_ref_at_all_is_unverifiable(self):
        # §0.1: unverifiable means NO #N anywhere in the subject (not "no trailing PR").
        subjects = ["feat: thing with no ref"]
        result = audit(subjects, "anything")
        self.assertEqual(len(result), 1)
        self.assertIsNone(result[0].pr)
        self.assertEqual(result[0].reason, "no #N reference")

    def test_issue_ref_covers_even_when_pr_does_not(self):
        # §0.1 core: CHANGELOG cites the ISSUE (#393); the trailing PR (#400) is
        # absent. ANY ref covering is enough — this must PASS.
        subjects = ["feat(socratic): probes (#393) (#400)"]
        unreleased = "- contribution probes (#393)\n"
        self.assertEqual(audit(subjects, unreleased), [])

    def test_uncovered_when_no_ref_is_in_unreleased(self):
        # neither the issue #393 nor the PR #400 is documented -> fail; the
        # trailing PR is the display id.
        subjects = ["feat(socratic): probes (#393) (#400)"]
        result = audit(subjects, "- unrelated (#1)\n")
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].pr, 400)
        self.assertEqual(result[0].reason, "not covered")

    def test_revert_covered_by_either_ref_passes(self):
        # §0.1: a revert carries both the reverted PR (#432) and the revert PR
        # (#433); coverage by EITHER counts (accepted loosening, §3.5).
        subjects = ['Revert "feat: thing (#432)" (#433)']
        self.assertEqual(audit(subjects, "- reverted thing (#433)\n"), [])
        self.assertEqual(audit(subjects, "- original thing (#432)\n"), [])

    def test_revert_uncovered_when_neither_ref_present(self):
        subjects = ['Revert "feat: thing (#432)" (#433)']
        result = audit(subjects, "- unrelated (#1)\n")
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].pr, 433)  # trailing PR is the display id

    def test_mixed_list_accumulates_in_order(self):
        subjects = [
            "chore: x (#7)",                      # exempt -> skip
            "feat: covered (#100)",               # required, covered -> pass
            "feat: uncovered (#200)",             # required -> fail
            "Harden thing no ref",                # no #N -> fail
            'Revert "feat: old (#432)" (#433)',   # revert, neither ref covered -> fail
        ]
        result = audit(subjects, "- covered (#100)\n")
        self.assertEqual(
            result,
            [
                Uncovered("feat: uncovered (#200)", 200, "not covered"),
                Uncovered("Harden thing no ref", None, "no #N reference"),
                Uncovered('Revert "feat: old (#432)" (#433)', 433, "not covered"),
            ],
        )


class ExtractUnreleasedTest(unittest.TestCase):
    CHANGELOG = textwrap.dedent("""\
        # Changelog

        ## [Unreleased]

        ### Added
        - thing (#432)

        ## [3.12.0] - 2026-06-08
        - old thing (#300)
        """)

    def test_extracts_only_unreleased_body(self):
        body = extract_unreleased(self.CHANGELOG)
        self.assertIn("#432", body)
        self.assertNotIn("#300", body)  # must stop at the next ## heading

    def test_missing_unreleased_returns_none(self):
        self.assertIsNone(extract_unreleased("# Changelog\n## [3.12.0]\n- x\n"))


from check_changelog_covers_merges import (  # noqa: E402
    previous_release_tag,
    merged_commit_subjects,
)

_GIT_ENV = {
    "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
    "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t",
}


def _git(repo: Path, *args: str) -> str:
    import os
    env = os.environ.copy()
    env.update(_GIT_ENV)
    return subprocess.run(
        ["git", "-C", str(repo), *args],
        capture_output=True, text=True, check=True, env=env,
    ).stdout.strip()


def _commit(repo: Path, subject: str) -> None:
    (repo / "f.txt").write_text(subject)
    _git(repo, "add", "f.txt")
    _git(repo, "commit", "-m", subject)


class ExtractCoverageTextTest(unittest.TestCase):
    CHANGELOG = textwrap.dedent(
        """\
        # Changelog

        ## [Unreleased]

        - pending thing (#900)

        ## [3.15.0] - 2026-07-10 — promoted by the release-prep PR

        - promoted thing (#901)

        ## [3.14.0] - 2026-07-02 — previous release

        - already-released thing (#902)
        """
    )

    def test_window_spans_unreleased_and_promoted_sections(self):
        window = extract_coverage_text(self.CHANGELOG, "v3.14.0")
        self.assertIn("#900", window)
        self.assertIn("#901", window)  # release-prep-promoted section counts

    def test_window_excludes_previous_release_and_below(self):
        window = extract_coverage_text(self.CHANGELOG, "v3.14.0")
        # A stale mention in already-released history must not cover a new
        # commit that reuses the same issue number.
        self.assertNotIn("#902", window)
        self.assertFalse(is_covered(902, window))

    def test_missing_previous_heading_returns_none(self):
        # Fail-closed: no silent widening of the window to the whole file.
        self.assertIsNone(extract_coverage_text(self.CHANGELOG, "v3.13.0"))

    def test_version_dots_not_regex_wildcards(self):
        # [3.14.0] must not be matched by a heading like [3.14x0].
        text = "## [3x14y0]\n- decoy (#903)\n"
        self.assertIsNone(extract_coverage_text(text, "v3.14.0"))

    def test_boundary_heading_line_itself_is_excluded(self):
        # A #N on the previous release's OWN heading line is released history,
        # not coverage (codex P3 pin: slice ends BEFORE the heading line).
        text = "## [Unreleased]\n\n## [3.14.0] - rework (#902)\n- body\n"
        window = extract_coverage_text(text, "v3.14.0")
        self.assertFalse(is_covered(902, window))


class GitInterfaceTest(unittest.TestCase):
    def _repo(self, stack):
        d = Path(stack.enter_context(TemporaryDirectory()))
        _git(d, "init", "-q")
        # Disable GPG signing in throwaway repos; the global tag.gpgSign=true
        # would otherwise force annotated-tag mode and require a -m message.
        _git(d, "config", "tag.gpgSign", "false")
        return d

    def test_previous_tag_and_subjects(self):
        import contextlib
        with contextlib.ExitStack() as stack:
            repo = self._repo(stack)
            _commit(repo, "feat: base (#1)")
            _git(repo, "tag", "v3.12.0")
            _commit(repo, "feat: new thing (#2)")
            _commit(repo, "chore: noise (#3)")
            # Pre-tag: HEAD has no new tag, so describe returns the prev tag.
            self.assertEqual(previous_release_tag(repo), "v3.12.0")
            subs = merged_commit_subjects(repo, "v3.12.0")
            self.assertIn("feat: new thing (#2)", subs)
            self.assertIn("chore: noise (#3)", subs)
            self.assertNotIn("feat: base (#1)", subs)

    def test_non_v_tags_ignored(self):
        import contextlib
        with contextlib.ExitStack() as stack:
            repo = self._repo(stack)
            _commit(repo, "feat: base (#1)")
            _git(repo, "tag", "v3.12.0")
            _git(repo, "tag", "nightly")  # non-v tag must be ignored
            _commit(repo, "feat: x (#2)")
            self.assertEqual(previous_release_tag(repo), "v3.12.0")

    def test_no_tags_returns_none(self):
        import contextlib
        with contextlib.ExitStack() as stack:
            repo = self._repo(stack)
            _commit(repo, "feat: base (#1)")
            self.assertIsNone(previous_release_tag(repo))


class CliEndToEndTest(unittest.TestCase):
    def _make_repo(self, stack, changelog_body):
        import os
        repo = Path(stack.enter_context(TemporaryDirectory()))
        env = os.environ.copy(); env.update(_GIT_ENV)
        subprocess.run(["git", "-C", str(repo), "init", "-q"], check=True, env=env)
        subprocess.run(["git", "-C", str(repo), "config", "tag.gpgSign", "false"], check=True, env=env)
        (repo / "CHANGELOG.md").write_text(changelog_body)
        subprocess.run(["git", "-C", str(repo), "add", "."], check=True, env=env)
        subprocess.run(["git", "-C", str(repo), "commit", "-q", "-m", "base (#1)"], check=True, env=env)
        subprocess.run(["git", "-C", str(repo), "tag", "v3.12.0"], check=True, env=env)
        return repo, env

    def _add_commit(self, repo, env, subject):
        (repo / "f.txt").write_text(subject)
        subprocess.run(["git", "-C", str(repo), "add", "f.txt"], check=True, env=env)
        subprocess.run(["git", "-C", str(repo), "commit", "-q", "-m", subject], check=True, env=env)

    def test_pass_when_covered(self):
        import contextlib
        with contextlib.ExitStack() as stack:
            cl = "# Changelog\n\n## [Unreleased]\n\n- new (#2)\n\n## [3.12.0]\n- old\n"
            repo, env = self._make_repo(stack, cl)
            self._add_commit(repo, env, "feat: new (#2)")
            proc = run_script(SCRIPT, "--repo", str(repo), cwd=repo)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_fail_when_uncovered(self):
        import contextlib
        with contextlib.ExitStack() as stack:
            cl = "# Changelog\n\n## [Unreleased]\n\n- unrelated (#9)\n\n## [3.12.0]\n- old\n"
            repo, env = self._make_repo(stack, cl)
            self._add_commit(repo, env, "feat: new (#2)")
            proc = run_script(SCRIPT, "--repo", str(repo), cwd=repo)
            self.assertEqual(proc.returncode, 1)
            self.assertIn("#2", proc.stdout + proc.stderr)

    def test_fail_closed_no_previous_tag(self):
        import contextlib, os
        with contextlib.ExitStack() as stack:
            repo = Path(stack.enter_context(TemporaryDirectory()))
            env = os.environ.copy(); env.update(_GIT_ENV)
            subprocess.run(["git", "-C", str(repo), "init", "-q"], check=True, env=env)
            (repo / "CHANGELOG.md").write_text("## [Unreleased]\n- x (#1)\n")
            subprocess.run(["git", "-C", str(repo), "add", "."], check=True, env=env)
            subprocess.run(["git", "-C", str(repo), "commit", "-q", "-m", "base (#1)"], check=True, env=env)
            # no tag at all -> fail closed (not first-release flag)
            proc = run_script(SCRIPT, "--repo", str(repo), cwd=repo)
            self.assertEqual(proc.returncode, 1)
            self.assertIn("no previous release tag", (proc.stdout + proc.stderr).lower())

    def test_first_release_flag_passes(self):
        import contextlib, os
        with contextlib.ExitStack() as stack:
            repo = Path(stack.enter_context(TemporaryDirectory()))
            env = os.environ.copy(); env.update(_GIT_ENV)
            subprocess.run(["git", "-C", str(repo), "init", "-q"], check=True, env=env)
            (repo / "CHANGELOG.md").write_text("## [Unreleased]\n- x (#1)\n")
            subprocess.run(["git", "-C", str(repo), "add", "."], check=True, env=env)
            subprocess.run(["git", "-C", str(repo), "commit", "-q", "-m", "base (#1)"], check=True, env=env)
            proc = run_script(SCRIPT, "--repo", str(repo), "--first-release", cwd=repo)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_fail_when_changelog_missing(self):
        import contextlib, os
        with contextlib.ExitStack() as stack:
            repo = Path(stack.enter_context(TemporaryDirectory()))
            env = os.environ.copy(); env.update(_GIT_ENV)
            subprocess.run(["git", "-C", str(repo), "init", "-q"], check=True, env=env)
            subprocess.run(["git", "-C", str(repo), "config", "tag.gpgSign", "false"], check=True, env=env)
            (repo / "f.txt").write_text("x")
            subprocess.run(["git", "-C", str(repo), "add", "."], check=True, env=env)
            subprocess.run(["git", "-C", str(repo), "commit", "-q", "-m", "base (#1)"], check=True, env=env)
            subprocess.run(["git", "-C", str(repo), "tag", "v3.12.0"], check=True, env=env)
            proc = run_script(SCRIPT, "--repo", str(repo), cwd=repo)
            self.assertEqual(proc.returncode, 1)
            self.assertIn("not found", proc.stdout + proc.stderr)

    def test_fail_when_no_unreleased_section(self):
        import contextlib
        with contextlib.ExitStack() as stack:
            cl = "# Changelog\n\n## [3.12.0]\n- old\n"  # no [Unreleased]
            repo, env = self._make_repo(stack, cl)
            self._add_commit(repo, env, "feat: new (#2)")
            proc = run_script(SCRIPT, "--repo", str(repo), cwd=repo)
            self.assertEqual(proc.returncode, 1)
            self.assertIn("[Unreleased]", proc.stdout + proc.stderr)

    def test_pass_when_covered_by_promoted_section(self):
        # §0.2: the release-prep PR promotes [Unreleased] into [3.13.0] before
        # the tag exists; entries there must still count as coverage.
        import contextlib
        with contextlib.ExitStack() as stack:
            cl = ("# Changelog\n\n## [Unreleased]\n\n"
                  "## [3.13.0] - promoted\n- new (#2)\n\n"
                  "## [3.12.0]\n- old\n")
            repo, env = self._make_repo(stack, cl)
            self._add_commit(repo, env, "feat: new (#2)")
            proc = run_script(SCRIPT, "--repo", str(repo), cwd=repo)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_stale_mention_below_boundary_does_not_cover(self):
        # §0.2 fail-closed precision: a #N in already-released history must not
        # cover a new commit that reuses the number.
        import contextlib
        with contextlib.ExitStack() as stack:
            cl = ("# Changelog\n\n## [Unreleased]\n\n"
                  "## [3.12.0]\n- ancient mention of (#2)\n")
            repo, env = self._make_repo(stack, cl)
            self._add_commit(repo, env, "feat: new (#2)")
            proc = run_script(SCRIPT, "--repo", str(repo), cwd=repo)
            self.assertEqual(proc.returncode, 1)
            self.assertIn("#2", proc.stdout + proc.stderr)

    def test_fail_when_previous_release_heading_missing(self):
        # Tag v3.12.0 exists but CHANGELOG has no [3.12.0] heading: fail loud,
        # never silently widen the window to the whole file.
        import contextlib
        with contextlib.ExitStack() as stack:
            cl = "# Changelog\n\n## [Unreleased]\n- new (#2)\n"
            repo, env = self._make_repo(stack, cl)
            self._add_commit(repo, env, "feat: new (#2)")
            proc = run_script(SCRIPT, "--repo", str(repo), cwd=repo)
            self.assertEqual(proc.returncode, 1)
            self.assertIn("coverage window", proc.stdout + proc.stderr)

    def test_bad_merges_ref_fails_closed(self):
        # A typo'd --merges-ref (or missing origin/main in CI) must FAIL, not
        # silently pass as an empty range (codex P1: fail-open reproduced).
        import contextlib
        with contextlib.ExitStack() as stack:
            cl = "# Changelog\n\n## [Unreleased]\n\n## [3.12.0]\n- old\n"
            repo, env = self._make_repo(stack, cl)
            self._add_commit(repo, env, "feat: new (#2)")
            proc = run_script(SCRIPT, "--repo", str(repo),
                              "--merges-ref", "does-not-exist", cwd=repo)
            self.assertEqual(proc.returncode, 1)
            self.assertIn("failing closed", (proc.stdout + proc.stderr).lower())

    def test_merges_ref_bounds_audited_range(self):
        # CI on a release-prep PR audits <tag>..origin/main, not the prep
        # branch's own in-flight commits.
        import contextlib
        with contextlib.ExitStack() as stack:
            cl = ("# Changelog\n\n## [Unreleased]\n- covered (#2)\n\n"
                  "## [3.12.0]\n- old\n")
            repo, env = self._make_repo(stack, cl)
            self._add_commit(repo, env, "feat: covered (#2)")
            covered_tip = subprocess.run(
                ["git", "-C", str(repo), "rev-parse", "HEAD"],
                check=True, env=env, capture_output=True, text=True,
            ).stdout.strip()
            self._add_commit(repo, env, "feat: uncovered in-flight work")
            proc = run_script(SCRIPT, "--repo", str(repo), cwd=repo)
            self.assertEqual(proc.returncode, 1)  # default HEAD sees it
            proc = run_script(SCRIPT, "--repo", str(repo),
                              "--merges-ref", covered_tip, cwd=repo)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
