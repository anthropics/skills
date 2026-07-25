# CHANGELOG-covers-merges release gate

**Date:** 2026-06-13
**Status:** design (implementation in progress)
**Motivation:** close the one release-discipline gap the existing version-consistency lint does not cover — *merged but undocumented*.

## §0 amendment (2026-06-14, sanity-run-driven — supersedes the §3.2/§3.5 body where they conflict)

### §0.1 Coverage namespace = ANY `#N` in the subject, not the trailing PR alone

The pre-amendment design (and the cross-model design review's C-point) treated the
**trailing `(#N)` (the PR number)** as the sole coverage identity, on the reasoning that
the GitHub squash suffix is the stable anchor. The first real-repo sanity run (Task 8)
**falsified that assumption against this repo's actual convention**: ARS writes CHANGELOG
`[Unreleased]` entries against the **issue / spec number** (`#393`, `#394`, `#89`), while
the squash commit subject carries that issue ref MID-subject and the PR number as the
trailing suffix (`feat(socratic): … (#393) (#400)`). Under trailing-PR-only matching,
~26 already-documented commits reported as uncovered (their issue ref `#393` was in
`[Unreleased]`; their PR `#400` was not) — a flood of false positives that would bury the
genuinely-missing entries.

**Resolution (owner-decided):** coverage matches if **ANY** `#N` in the subject — trailing
PR suffix OR mid-subject issue/spec ref — appears in `[Unreleased]`. `audit` collects
`all_refs(subject)` and a commit is covered when any of them is present; `unverifiable`
now means "no `#N` at all in the subject" (not "no trailing PR"). The trailing
`pr_number` is retained purely as the report **display id**.

**Accepted trade-off (the C-point risk, eyes open):** a stale umbrella ref (e.g. a tracking
issue `#89` mentioned in an old `[Unreleased]` line) can now spuriously "cover" an
unrelated new commit that also cites `#89`. This is real but (a) `#89`-style umbrella refs
ARE the repo convention, and (b) the sanity run showed the false-POSITIVE rate under
trailing-PR-only was overwhelmingly larger than this false-NEGATIVE tail. For a pre-tag
*reminder* gate, under-reporting a `#89`-shadowed commit is far cheaper than drowning the
real misses. Mitigated, not eliminated; stated rather than hidden.

This amendment is sanity-run evidence over paper reasoning — the same lesson the title-match
work logged: a metadata/identity heuristic that looks right on synthetic cases must be run
against real data before it is trusted.

### §0.2 Coverage window = CHANGELOG above the previous release's section, not [Unreleased] alone (2026-07-02, practice-driven)

§3.1's pre-tag reasoning assumed entries stay under `[Unreleased]` until the tag is cut.
The v3.14.0 release **falsified that assumption against this repo's actual release flow**:
the release-prep PR (#481) promotes `[Unreleased]` into the new `## [X.Y.Z]` section
BEFORE the tag exists (promotion happens in the prep PR; the tag lands after its merge).
Under `[Unreleased]`-only scanning, the gate run on a prep PR (or on main between
prep-merge and tag push) false-flags every just-promoted entry — the gate would fail
exactly at the moment it is supposed to certify.

**Resolution:** the coverage window is the CHANGELOG text **above the previous release's
own heading** (`## [<prev version>]`, located from the git-derived previous tag). That
window contains `[Unreleased]` AND any release-prep-promoted newer section, in both the
during-development and prep-PR states; anything at or below the boundary is
already-released history, so a stale `#N` there cannot cover a new commit (this actually
NARROWS the §0.1 umbrella-ref trade-off for old refs). Fail-closed: if the previous
release's heading is missing, the gate errors instead of silently widening the window.

**Two operational consequences:**

- **`--merges-ref` (CI split):** the release-prep-PR CI job audits merges in
  `<prev_tag>..origin/main` while reading the PR checkout's CHANGELOG — the prep branch's
  own in-flight commits are not merges yet and would otherwise report unverifiable.
  Manual runs keep the HEAD default.
- **`docs(release)` exemption (and deliberately NOT `docs(i18n)`):** the once-per-release
  doc-alignment/promotion commit IS the changelog being written; it cannot cite itself and
  is exempt like `chore`/`ci` (added to `_EXEMPT_DOCS_SCOPES`; the scope is reserved for
  release mechanics by convention). `docs(i18n)` was considered and REJECTED (codex review
  P2, 2026-07-02): translation changes are user-facing docs like any other, so exempting
  the scope would let them slip through undocumented.

CI wiring shipped with this amendment: `.github/workflows/changelog-covers-merges.yml`
runs the gate on every `release/**`-headed PR into main (`fetch-depth: 0` +
`fetch-tags: true`); the CONTRIBUTING manual step remains for tag flows that skip a
release branch.

## 1. Problem

The repo releases via annotated `v*` tags. `CHANGELOG.md` keeps a `## [Unreleased]`
section that accumulates entries between releases and is promoted to `## [X.Y.Z]` at
tag time. A past release (the v3.11.1→v3.12.0 window) shipped with ~12 merged PRs that
were never written into CHANGELOG; they slipped through because `scripts/check_version_consistency.py`
only checks that the latest `## [X.Y.Z]` header equals the suite version — it never
checks that the in-progress release notes actually **cover everything merged since the
last tag**. Invariants 1–8 are all pure file reads; none touches git history, so the
"merged but undocumented" class has no guard.

This is the `check_version_consistency.py` invariant-4-to-6 follow-up named in the global
release-discipline rule, specialized to the dimension that was actually load-bearing in
the miss: not *which docs are aligned*, but *which merges were documented*.

## 2. Scope

**In scope:** a standalone `scripts/check_changelog_covers_merges.py` that, run **before
a release tag is cut**, verifies every release-worthy commit since the previous release
tag is referenced in the `## [Unreleased]` section of `CHANGELOG.md`.

**Out of scope:** changing `check_version_consistency.py` (its 8 invariants stay
byte-identical); a GitHub-API/label-based mechanism (rejected — needs network + auth in
CI, the local convention is strict enough; recorded in §8); auto-fixing CHANGELOG; any
post-tag enforcement (see §4 on why pre-tag is the real gate).

## 3. Design

### 3.1 Run mode — pre-tag only

The lint runs in **pre-tag mode**: invoked on the release-prep state *before* the `vX.Y.Z`
tag exists (manually as the release checklist step, and/or in a CI job that does not
depend on the tag ref). This choice is load-bearing — it dissolves the two hardest bugs
a post-tag design would carry (cross-model design review, 2026-06-13):

- **Section-to-scan ambiguity disappears.** Pre-tag, the entries still live under
  `## [Unreleased]` (not yet promoted to `## [X.Y.Z]`), so the lint scans `[Unreleased]`
  unconditionally. A post-tag design would have to scan the just-cut `[X.Y.Z]` section,
  which false-positives the moment promotion ordering varies.
- **Previous-tag selection becomes trivial.** Pre-tag, `HEAD` carries no new release tag,
  so the most-recent reachable release tag *is* the previous release. `git describe`
  returns it directly; no `HEAD^` dance, no "current tag == new tag → empty range" trap.

Process note (cross-model review): an `on: tags` CI job can only block *downstream*
publish, never the tag's existence. Pre-tag mode is therefore the genuine gate; a
post-tag CI copy, if ever added, is a belt-and-suspenders warning, not the primary
enforcement.

### 3.2 Architecture — two separable units

**Unit A — git interface (impure, thin):**
- `previous_release_tag() -> str | None`: `git describe --tags --abbrev=0 --match 'v[0-9]*'`,
  result validated against the accepted version grammar (§3.3). Returns `None` only in the
  explicit first-release case.
- `merged_commit_subjects(since_tag: str) -> list[str]`:
  `git log --first-parent --format=%s <since_tag>..HEAD`. `--first-parent` keeps the
  squash-merge mainline and ignores any merge-commit's second-parent noise.
- **Fail-closed:** shallow checkout / no tags / git error → exit with a clear diagnostic,
  never a silent pass.

**Unit B — coverage logic (pure, fully tested):**
- `pr_number(subject: str) -> int | None`: the **trailing** `(#N)` of the subject (the
  GitHub squash suffix). Used as the commit's *display identity* in reports, and — together
  with `all_refs` — to decide verifiability.
- `all_refs(subject: str) -> list[int]`: **every** `#N` in the subject — the trailing PR
  suffix AND any mid-subject issue/spec refs (`(#89 Item 8)`, `(#393)`). This is the
  coverage namespace (see §0.1 amendment: this repo writes CHANGELOG entries against the
  **issue** number, not the PR number).
- `is_exempt(subject: str) -> bool`: conventional-commit type/scope parse (§3.4).
- `is_covered(ref: int, unreleased_text: str) -> bool`: token-aware membership — the
  number appears in `[Unreleased]` delimited by a non-digit on the right (`#42` must NOT
  match `#420`). The leading `#` is required, so a bare year/number in prose cannot
  spuriously cover.
- `audit(subjects, unreleased_text) -> list[Uncovered]`: for each non-exempt subject,
  collect `all_refs`; **no `#N` at all → `unverifiable` (a failure, not a skip)**; if NONE
  of its refs appears in `[Unreleased]` → `uncovered`; if ANY ref appears → covered.
  Return the failures, each carrying the trailing `pr_number` (or None) as its display id.

Unit B never calls git. Tests feed synthetic subject lists + synthetic CHANGELOG text.

### 3.3 Version grammar (tag matching)

Accept the repo's real tag shapes, not just `X.Y.Z`. Observed: `v2.8`, `v3.9.4.2`,
`v3.12.0`. Grammar: `v` + 2-to-4 dot-separated integer segments. `--match 'v[0-9]*'`
pre-filters at the git layer; a script-level regex (`^v\d+(\.\d+){1,3}$`) is the
authority. Prerelease/non-`v`/nonstandard tags are ignored for previous-tag selection.
First release (no matching previous tag): pass with an explicit "no previous release tag —
treating all history as the first release" diagnostic ONLY under an explicit
`--first-release` flag; otherwise fail closed (a missing previous tag is far more often a
shallow-checkout bug than a genuine first release).

### 3.4 Exemption rule (which commits need not be documented)

Parse the conventional-commit prefix `type` and optional `(scope)`:
`^(?P<type>[a-z]+)(?:\((?P<scope>[^)]*)\))?!?:`

- **Exempt by type:** `chore`, `test`, `ci`, `build` (pure-engineering; never user-facing).
  Scope-tolerant (`ci(scope):` is still `ci`).
- **Exempt by type+scope:** `docs(design)`, `docs(superpowers)` — internal design / spec
  docs that legitimately do not belong in a user-facing CHANGELOG.
- **Required (must be covered):** everything else — `feat`, `fix`, **bare `docs:`**, other
  `docs(scope):` (e.g. `docs(contributing)`, `docs(positioning)`), `refactor`, `perf`,
  AND **no-prefix subjects** (the repo has real no-prefix release-worthy commits, e.g.
  `Harden title-fallback … (#432)`).

Deliberately NOT exempt: `refactor:`, `perf:`, broad `docs:`. Broadening the exempt set
is how the original failure mode reopens under different prefixes (cross-model review).
The `docs(design)`/`docs(superpowers)` carve-out is the *narrowest* scope that removes the
known false-positive class without reopening the recall hole — bare `docs:` and every
other docs scope stay required, honoring the owner decision that "docs must be covered"
(the missed-12 batch included docs-class entries).

### 3.5 Revert policy

`Revert "…"` commits are a real change to the released surface and must be covered. Under
the §0.1 any-ref model, a revert subject `Revert "feat: thing (#432)" (#433)` carries both
`#432` (the reverted PR) and `#433` (the revert PR); coverage by EITHER counts. This is a
deliberate, accepted loosening from the pre-amendment "own-PR-only" rule: a revert whose
CHANGELOG entry references the original PR number is documented in practice, and chasing
the stricter own-PR-only rule conflicts with the repo's issue-keyed CHANGELOG convention
(§0.1). The trailing `(#433)` remains the revert's display id in reports.

### 3.6 Output

- Pass: one line, "`N` release-worthy commit(s) since `<tag>`, all covered."
- Fail: per uncovered/unverifiable commit, `<#N or NO-PR>  <subject>` + a reason
  (`not in [Unreleased]` / `no trailing (#N)`), then a one-line remediation
  ("add a CHANGELOG `[Unreleased]` entry citing the PR number, or mark the commit exempt
  via an accepted conventional prefix"). Exit 1.

## 4. CI wiring

A `release-gate` style step. The repo already has `on: tags` workflows
(`release-cooldown.yml`, `defer-label-gate.yml`); this lint is the **pre-tag** complement.
Concretely: add it to the release checklist (manual `python3 scripts/check_changelog_covers_merges.py`
before tagging) and, if a pre-tag CI hook is wanted, a workflow that runs on a release-prep
branch/PR (NOT `on: tags`, since that fires too late). Needs `fetch-depth: 0` +
`fetch-tags: true` (mirrors `release-cooldown.yml`). The global release-discipline rule's
`[doc-aligned: yyyy-mm-dd]` tag-message step remains the human confirmation; this lint
makes the Unreleased-coverage invariant machine-checked.

## 5. Testing

- **Unit B (pure):** synthetic subject-list × synthetic CHANGELOG matrix —
  trailing-`(#N)` extraction, mid-subject-ref ignored, `#42`≠`#420` token boundary,
  every exempt/required prefix branch, no-prefix→required, no-trailing-PR→unverifiable,
  revert→own-PR-required, scoped-conventional (`ci(x):`, `docs(design):`).
- **Unit A (git, deterministic temp repo):** build a throwaway `git init` repo in a
  tmpdir with hand-authored tags + commits (cross-model review's named requirement — never
  the live repo, whose history drifts). Cover: previous-tag selection picks the right
  earlier tag; non-`v`/prerelease tags ignored; first-release flag; fail-closed on no tags.
- **Acceptance against live repo (informational, not a unit test):** at design time the
  real `[Unreleased]` already references the post-v3.12.0 PRs (#423/#426/#429/#430/#432
  etc.), so a real run should PASS today — a quick manual sanity check, not a pinned test.

## 6. Self-review notes

- No placeholders.
- Pre-tag mode (§3.1) and the git-interface design (§3.2) are consistent: both assume
  HEAD has no new tag yet.
- Scope is a single script + tests + optional CI step — one implementation plan.
- The one ambiguity worth pinning: "release-worthy" = non-exempt by §3.4, with no-prefix
  defaulting to required (made explicit there).

## 7. Cross-model design review (codex gpt-5.5 xhigh, 2026-06-13)

Verdict: **DESIGN SOUND WITH FIXES.** All must-fix items folded in:
- A/B (section-scan + previous-tag hard bugs) → dissolved by choosing pre-tag mode (§3.1).
- C (`#N` too loose) → trailing-`(#N)` identity + token-aware match (§3.2 Unit B).
- D (skip rule) → narrow `docs(design)/docs(superpowers)` scope carve-out, no broad
  exemption (§3.4).
- E (revert/merge/no-prefix) → `--first-parent`, revert-own-PR policy, no-trailing-PR =
  unverifiable-not-skip (§3.2/§3.5).
- Process hole (`on: tags` can't block the tag) → pre-tag is the real gate (§3.1/§4).
- Tag-selection tested via deterministic temp git repos (§5).

## 8. Rejected alternative

**GitHub PR labels (`changelog-required` / `no-changelog`) via API/GraphQL.** Semantically
the strongest "was this documented" signal and avoids subject scraping. Rejected for now:
needs network + auth + CI token permissions + rate-limit handling, against the stdlib-only
constraint. Revisit only if the commit-subject convention proves too weak in practice;
the convention is already strict (every squash carries a trailing `(#N)`).
