"""Pre-tag lint: every release-worthy commit since the previous release tag
must be referenced in CHANGELOG.md ABOVE the previous release's own section
(the pre-tag coverage window: [Unreleased] plus any already-promoted newer
version section — §0.2).

Closes the "merged but undocumented" gap that check_version_consistency.py
(invariants 1-8, pure file reads) does not cover. Runs in PRE-TAG mode: before
the vX.Y.Z tag exists, `git describe` returns the PREVIOUS release tag
directly. Entries may sit under [Unreleased] (normal development) or under the
release-prep-promoted [X.Y.Z] section (this repo promotes in the release-prep
PR before tagging — v3.14.0 / PR #481 precedent); both are above the previous
release's heading, and stale mentions below it never cover a new commit.

Spec: docs/design/2026-06-13-changelog-covers-merges-release-gate-spec.md.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

# The trailing `(#N)` (the GitHub squash suffix) — used as a commit's DISPLAY id.
_TRAILING_PR_RE = re.compile(r"\(#(\d+)\)\s*$")
# Every `#N` token anywhere in the subject — the COVERAGE namespace (§0.1): this
# repo writes CHANGELOG entries against the issue/spec number, which appears
# mid-subject, not as the trailing PR suffix.
_ANY_REF_RE = re.compile(r"#(\d+)")


def pr_number(subject: str) -> int | None:
    """Return the trailing `(#N)` PR number of a commit subject, or None.

    This is the commit's DISPLAY identity in reports. Coverage uses `all_refs`
    (any `#N`), not this — see §0.1."""
    m = _TRAILING_PR_RE.search(subject.rstrip())
    return int(m.group(1)) if m else None


def all_refs(subject: str) -> list[int]:
    """Every `#N` in the subject — the trailing PR suffix AND any mid-subject
    issue/spec refs (`(#89 Item 8)`, `(#393)`). This is the coverage namespace
    (§0.1): a commit is covered if ANY of these appears in [Unreleased], because
    the repo writes CHANGELOG entries against the issue number, not the PR."""
    return [int(n) for n in _ANY_REF_RE.findall(subject)]


# Conventional-commit prefix: type + optional (scope) + optional ! + colon.
_PREFIX_RE = re.compile(r"^(?P<type>[a-z]+)(?:\((?P<scope>[^)]*)\))?!?:")

# Pure-engineering types — never user-facing.
_EXEMPT_TYPES = frozenset({"chore", "test", "ci", "build"})
# Internal design/spec docs that do not belong in a user-facing CHANGELOG,
# plus docs(release): the once-per-release doc-alignment/promotion commit IS
# the changelog being written — it cannot cite itself. The scope is reserved
# for release mechanics by convention; docs(i18n) is deliberately NOT exempt
# (translation changes are user-facing docs like any other — codex review P2).
_EXEMPT_DOCS_SCOPES = frozenset({"design", "superpowers", "release"})


def is_covered(ref: int, coverage_text: str) -> bool:
    """True iff `#<ref>` appears in the coverage window delimited by a non-digit
    on the right (so `#42` does not match `#420`). The leading `#` is required,
    so a bare number in prose cannot spuriously cover."""
    pattern = re.compile(r"#" + str(ref) + r"(?!\d)")
    return pattern.search(coverage_text) is not None


def is_exempt(subject: str) -> bool:
    """True iff the commit need not be referenced in CHANGELOG.

    Exempt: chore/test/ci/build (any scope), and docs(design)/docs(superpowers).
    Everything else — feat, fix, bare docs, other docs scopes, refactor, perf,
    AND no-prefix subjects — is REQUIRED. Broadening this set reopens the
    original "merged but undocumented" failure mode under different prefixes.
    """
    m = _PREFIX_RE.match(subject)
    if not m:
        return False  # no-prefix subjects are required
    ctype = m.group("type")
    scope = m.group("scope")
    if ctype in _EXEMPT_TYPES:
        return True
    if ctype == "docs" and scope in _EXEMPT_DOCS_SCOPES:
        return True
    return False


@dataclass(frozen=True)
class Uncovered:
    subject: str
    pr: int | None  # display id (trailing PR), None when the subject has no #N
    reason: str  # "not in [Unreleased]" | "no #N reference"


def audit(subjects: list[str], coverage_text: str) -> list[Uncovered]:
    """Return the release-worthy commits not provably covered by the pre-tag
    coverage window (CHANGELOG text above the previous release's section).

    Coverage uses ANY `#N` in the subject (§0.1): trailing PR OR mid-subject
    issue/spec ref. A subject with NO `#N` at all is `unverifiable` (a failure,
    not a skip): we cannot prove coverage, so it must be made exempt or given a
    reference. `pr` carries the trailing PR as the report display id (or None).
    """
    failures: list[Uncovered] = []
    for subject in subjects:
        if is_exempt(subject):
            continue
        refs = all_refs(subject)
        if not refs:
            failures.append(Uncovered(subject, None, "no #N reference"))
            continue
        if not any(is_covered(ref, coverage_text) for ref in refs):
            failures.append(Uncovered(subject, pr_number(subject), "not covered"))
    return failures


# The [Unreleased] section: from its heading to the next top-level `## ` heading.
_UNRELEASED_RE = re.compile(
    r"^##\s*\[Unreleased\]\s*$(?P<body>.*?)(?=^##\s|\Z)",
    re.MULTILINE | re.DOTALL | re.IGNORECASE,
)


def extract_unreleased(changelog_text: str) -> str | None:
    """Return the body text under `## [Unreleased]` up to the next `## ` heading,
    or None if there is no Unreleased section."""
    m = _UNRELEASED_RE.search(changelog_text)
    return m.group("body") if m else None


def extract_coverage_text(changelog_text: str, previous_tag: str) -> str | None:
    """Return the CHANGELOG text ABOVE the previous release's own section
    heading — the pre-tag coverage window (§0.2).

    Pre-tag, a release-worthy commit may be documented under
    ``## [Unreleased]`` (normal development) or under an already-promoted
    newer ``## [X.Y.Z]`` section (this repo's release-prep PRs promote
    Unreleased BEFORE the tag exists — v3.14.0 / PR #481 precedent). Both
    live above the previous release's heading; anything at or below it is
    already-released history, so a stale mention there must not cover a new
    commit. None when the previous release's heading is missing
    (fail-closed: the caller reports instead of widening the window)."""
    version = previous_tag.lstrip("v")
    m = re.search(
        r"^##\s*\[" + re.escape(version) + r"\]",
        changelog_text,
        re.MULTILINE,
    )
    if m is None:
        return None
    return changelog_text[: m.start()]


_TAG_GRAMMAR_RE = re.compile(r"^v\d+(?:\.\d+){1,3}$")


def _git_out(repo: Path, *args: str) -> str | None:
    """Run git in `repo`, return stdout stripped, or None on non-zero exit."""
    try:
        proc = subprocess.run(
            ["git", "-C", str(repo), *args],
            capture_output=True, text=True, check=True,
        )
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None
    return proc.stdout.strip()


def previous_release_tag(repo: Path) -> str | None:
    """Most recent release tag reachable from HEAD (pre-tag mode: HEAD has no
    new tag, so this IS the previous release). Restricted to the v-tag grammar;
    non-v / nonstandard tags are ignored. None when no matching tag exists."""
    out = _git_out(repo, "describe", "--tags", "--abbrev=0", "--match", "v[0-9]*")
    if out is None or not _TAG_GRAMMAR_RE.match(out):
        return None
    return out


def merged_commit_subjects(repo: Path, since_tag: str, ref: str = "HEAD") -> list[str] | None:
    """First-parent commit subjects in `<since_tag>..<ref>`, or None when the
    git invocation itself fails (bad ref / shallow checkout). None is NOT an
    empty range — the caller must fail closed, else a typo'd --merges-ref or a
    missing origin/main in CI silently passes the gate (codex review P1)."""
    out = _git_out(repo, "log", "--first-parent", "--format=%s", f"{since_tag}..{ref}")
    if out is None:
        return None
    if not out:
        return []
    return out.splitlines()


def check(repo: Path, *, first_release: bool = False, merges_ref: str = "HEAD") -> list[str]:
    """Return a list of error lines; empty means the gate passes.

    ``merges_ref`` bounds the audited merge range (`<prev_tag>..<merges_ref>`).
    Default HEAD suits the manual pre-tag run; the release-prep-PR CI job
    passes ``origin/main`` so only merges already landed on main are audited
    (the prep branch's own in-flight commits are not merges yet), while the
    coverage window still reads the PR's CHANGELOG state."""
    errors: list[str] = []

    changelog = repo / "CHANGELOG.md"
    if not changelog.is_file():
        return [f"{changelog}: not found"]
    changelog_text = changelog.read_text(encoding="utf-8")
    if extract_unreleased(changelog_text) is None:
        return ["CHANGELOG.md: no '## [Unreleased]' section to verify against"]

    tag = previous_release_tag(repo)
    if tag is None:
        if first_release:
            return []  # explicit first-release: nothing to compare against
        return [
            "no previous release tag found (expected a vX.Y.Z tag reachable "
            "from HEAD). If this is genuinely the first release, pass "
            "--first-release; otherwise this is usually a shallow checkout "
            "(fetch-depth: 0 + fetch-tags: true)."
        ]

    coverage = extract_coverage_text(changelog_text, tag)
    if coverage is None:
        return [
            f"CHANGELOG.md: no '## [{tag.lstrip('v')}]' section for the "
            f"previous release {tag} — cannot bound the pre-tag coverage "
            "window (fix the heading, or the tag grammar)."
        ]

    subjects = merged_commit_subjects(repo, tag, merges_ref)
    if subjects is None:
        return [
            f"git log {tag}..{merges_ref} failed — cannot enumerate the merges "
            "to audit (bad --merges-ref, or refs/tags missing in a shallow "
            "checkout). Failing closed."
        ]
    failures = audit(subjects, coverage)
    for f in failures:
        ident = f"#{f.pr}" if f.pr is not None else "NO-PR"
        errors.append(f"  {ident}  {f.subject}  [{f.reason}]")
    if errors:
        required = sum(1 for s in subjects if not is_exempt(s))
        errors.insert(
            0,
            f"{len(failures)} of {required} release-worthy commit(s) since "
            f"{tag} are not referenced in CHANGELOG above the [{tag.lstrip('v')}] "
            "section ([Unreleased] or a newer version section):",
        )
        errors.append(
            "  Fix: add a CHANGELOG entry (under [Unreleased], or the "
            "release-prep-promoted section) citing the commit's issue or PR "
            "number (#N), or mark the commit exempt via an accepted "
            "conventional prefix."
        )
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Pre-tag lint: CHANGELOG (above the previous release's "
        "section) must cover every release-worthy commit since the previous "
        "release tag."
    )
    parser.add_argument("--repo", default=".", help="Repo root (default: cwd).")
    parser.add_argument(
        "--first-release", action="store_true",
        help="No previous release tag is expected (first release).",
    )
    parser.add_argument(
        "--merges-ref", default="HEAD",
        help="Audit merges in <prev_tag>..<this ref> (default HEAD). The "
        "release-prep-PR CI job passes origin/main.",
    )
    args = parser.parse_args(argv)
    errors = check(
        Path(args.repo),
        first_release=args.first_release,
        merges_ref=args.merges_ref,
    )
    if errors:
        print("\n".join(errors))
        return 1
    print("CHANGELOG covers all release-worthy commits since the previous tag.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
